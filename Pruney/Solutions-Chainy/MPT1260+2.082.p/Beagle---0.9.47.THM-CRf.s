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
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 11.72s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 542 expanded)
%              Number of leaves         :   36 ( 196 expanded)
%              Depth                    :   15
%              Number of atoms          :  212 (1185 expanded)
%              Number of equality atoms :   67 ( 288 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_68,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_91])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_345,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_423,plain,(
    ! [B_104,A_105,C_106] :
      ( k7_subset_1(B_104,A_105,C_106) = k4_xboole_0(A_105,C_106)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(resolution,[status(thm)],[c_20,c_345])).

tff(c_451,plain,(
    ! [A_107,B_108,C_109] : k7_subset_1(A_107,k4_xboole_0(A_107,B_108),C_109) = k4_xboole_0(k4_xboole_0(A_107,B_108),C_109) ),
    inference(resolution,[status(thm)],[c_2,c_423])).

tff(c_469,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_109) = k4_xboole_0(k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2'),C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_451])).

tff(c_478,plain,(
    ! [C_109] : k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_109) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),C_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_469])).

tff(c_16,plain,(
    ! [A_19] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_69,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,B_63) = B_63
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_19,B_63] : k9_subset_1(A_19,B_63,B_63) = B_63 ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_904,plain,(
    ! [A_141,B_142,C_143] :
      ( k9_subset_1(A_141,B_142,k3_subset_1(A_141,C_143)) = k7_subset_1(A_141,B_142,C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(A_141))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_941,plain,(
    ! [B_146] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_146,k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k7_subset_1(u1_struct_0('#skF_1'),B_146,'#skF_2')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_904])).

tff(c_955,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_941])).

tff(c_959,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_955])).

tff(c_1318,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_1442,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_1318])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1442])).

tff(c_1451,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_32,plain,(
    ! [C_47,A_35,D_49,B_43] :
      ( v3_pre_topc(C_47,A_35)
      | k1_tops_1(A_35,C_47) != C_47
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0(B_43)))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1766,plain,(
    ! [D_178,B_179] :
      ( ~ m1_subset_1(D_178,k1_zfmisc_1(u1_struct_0(B_179)))
      | ~ l1_pre_topc(B_179) ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_1769,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1451,c_1766])).

tff(c_1787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1769])).

tff(c_1887,plain,(
    ! [C_185,A_186] :
      ( v3_pre_topc(C_185,A_186)
      | k1_tops_1(A_186,C_185) != C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1904,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1887])).

tff(c_1917,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1904])).

tff(c_1918,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1917])).

tff(c_703,plain,(
    ! [A_130,B_131] :
      ( m1_subset_1(k2_pre_topc(A_130,B_131),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_subset_1(A_10,k3_subset_1(A_10,B_11)) = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_724,plain,(
    ! [A_130,B_131] :
      ( k3_subset_1(u1_struct_0(A_130),k3_subset_1(u1_struct_0(A_130),k2_pre_topc(A_130,B_131))) = k2_pre_topc(A_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_703,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k3_subset_1(A_3,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5158,plain,(
    ! [A_259,B_260] :
      ( k4_xboole_0(u1_struct_0(A_259),k2_pre_topc(A_259,B_260)) = k3_subset_1(u1_struct_0(A_259),k2_pre_topc(A_259,B_260))
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_703,c_4])).

tff(c_5170,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_5158])).

tff(c_5182,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5170])).

tff(c_129,plain,(
    ! [B_71,A_72] :
      ( k4_xboole_0(B_71,A_72) = k3_subset_1(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_282,plain,(
    ! [A_91,B_92] : k4_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_subset_1(A_91,k4_xboole_0(A_91,B_92)) ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_291,plain,(
    ! [A_91,B_92] : r1_tarski(k3_subset_1(A_91,k4_xboole_0(A_91,B_92)),A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_2])).

tff(c_5242,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'))),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5182,c_291])).

tff(c_5491,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_5242])).

tff(c_5510,plain,(
    r1_tarski(k2_pre_topc('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_5491])).

tff(c_355,plain,(
    ! [B_21,A_20,C_98] :
      ( k7_subset_1(B_21,A_20,C_98) = k4_xboole_0(A_20,C_98)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_345])).

tff(c_5536,plain,(
    ! [C_264] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_264) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_264) ),
    inference(resolution,[status(thm)],[c_5510,c_355])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_124,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_50])).

tff(c_5550,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5536,c_124])).

tff(c_5603,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5550,c_2])).

tff(c_356,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_98) = k4_xboole_0('#skF_2',C_98) ),
    inference(resolution,[status(thm)],[c_38,c_345])).

tff(c_753,plain,(
    ! [A_136,B_137] :
      ( k7_subset_1(u1_struct_0(A_136),B_137,k2_tops_1(A_136,B_137)) = k1_tops_1(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_763,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_753])).

tff(c_772,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_356,c_763])).

tff(c_489,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(B_112,k2_pre_topc(A_113,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_497,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_489])).

tff(c_505,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_497])).

tff(c_513,plain,(
    ! [C_98] : k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2',C_98) = k4_xboole_0('#skF_2',C_98) ),
    inference(resolution,[status(thm)],[c_505,c_355])).

tff(c_101,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(B_21,A_20) = k3_subset_1(B_21,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_514,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_505,c_101])).

tff(c_5575,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5550,c_514])).

tff(c_166,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_176,plain,(
    ! [B_21,A_20] :
      ( k3_subset_1(B_21,k3_subset_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_166])).

tff(c_5680,plain,
    ( k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5575,c_176])).

tff(c_5705,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_5680])).

tff(c_5686,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5575,c_6])).

tff(c_12751,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5686])).

tff(c_12754,plain,(
    ~ r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_12751])).

tff(c_12758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_12754])).

tff(c_12759,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5686])).

tff(c_4433,plain,(
    ! [B_245,B_246,A_247] :
      ( k9_subset_1(B_245,B_246,k3_subset_1(B_245,A_247)) = k7_subset_1(B_245,B_246,A_247)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(B_245))
      | ~ r1_tarski(A_247,B_245) ) ),
    inference(resolution,[status(thm)],[c_20,c_904])).

tff(c_13023,plain,(
    ! [A_358,B_359,A_360] :
      ( k9_subset_1(A_358,k3_subset_1(A_358,B_359),k3_subset_1(A_358,A_360)) = k7_subset_1(A_358,k3_subset_1(A_358,B_359),A_360)
      | ~ r1_tarski(A_360,A_358)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(A_358)) ) ),
    inference(resolution,[status(thm)],[c_6,c_4433])).

tff(c_17981,plain,(
    ! [A_438,A_439] :
      ( k7_subset_1(A_438,k3_subset_1(A_438,A_439),A_439) = k3_subset_1(A_438,A_439)
      | ~ r1_tarski(A_439,A_438)
      | ~ m1_subset_1(A_439,k1_zfmisc_1(A_438)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13023,c_78])).

tff(c_17989,plain,
    ( k7_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12759,c_17981])).

tff(c_18023,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5603,c_772,c_513,c_5705,c_5705,c_17989])).

tff(c_18025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1918,c_18023])).

tff(c_18026,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_18027,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_34,plain,(
    ! [B_43,D_49,C_47,A_35] :
      ( k1_tops_1(B_43,D_49) = D_49
      | ~ v3_pre_topc(D_49,B_43)
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0(B_43)))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(B_43)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_19529,plain,(
    ! [C_553,A_554] :
      ( ~ m1_subset_1(C_553,k1_zfmisc_1(u1_struct_0(A_554)))
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_19543,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_19529])).

tff(c_19553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_19543])).

tff(c_19661,plain,(
    ! [B_557,D_558] :
      ( k1_tops_1(B_557,D_558) = D_558
      | ~ v3_pre_topc(D_558,B_557)
      | ~ m1_subset_1(D_558,k1_zfmisc_1(u1_struct_0(B_557)))
      | ~ l1_pre_topc(B_557) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_19678,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_19661])).

tff(c_19691,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18027,c_19678])).

tff(c_30,plain,(
    ! [A_32,B_34] :
      ( k7_subset_1(u1_struct_0(A_32),k2_pre_topc(A_32,B_34),k1_tops_1(A_32,B_34)) = k2_tops_1(A_32,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_19706,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19691,c_30])).

tff(c_19713,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_19706])).

tff(c_19715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18026,c_19713])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:08:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.72/4.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/4.99  
% 11.82/4.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/4.99  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.82/4.99  
% 11.82/4.99  %Foreground sorts:
% 11.82/4.99  
% 11.82/4.99  
% 11.82/4.99  %Background operators:
% 11.82/4.99  
% 11.82/4.99  
% 11.82/4.99  %Foreground operators:
% 11.82/4.99  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.82/4.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.82/4.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.82/4.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.82/4.99  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 11.82/4.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.82/4.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.82/4.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.82/4.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.82/4.99  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.82/4.99  tff('#skF_2', type, '#skF_2': $i).
% 11.82/4.99  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.82/4.99  tff('#skF_1', type, '#skF_1': $i).
% 11.82/4.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.82/4.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.82/4.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.82/4.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.82/4.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.82/4.99  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.82/4.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.82/4.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.82/4.99  
% 11.82/5.01  tff(f_134, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 11.82/5.01  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 11.82/5.01  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.82/5.01  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.82/5.01  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.82/5.01  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.82/5.01  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 11.82/5.01  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 11.82/5.01  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.82/5.01  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 11.82/5.01  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 11.82/5.01  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 11.82/5.01  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 11.82/5.01  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 11.82/5.01  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 11.82/5.01  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.82/5.01  tff(c_68, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 11.82/5.01  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.82/5.01  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.82/5.01  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.82/5.01  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.82/5.01  tff(c_91, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.82/5.01  tff(c_102, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_91])).
% 11.82/5.01  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.82/5.01  tff(c_20, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.82/5.01  tff(c_345, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.82/5.01  tff(c_423, plain, (![B_104, A_105, C_106]: (k7_subset_1(B_104, A_105, C_106)=k4_xboole_0(A_105, C_106) | ~r1_tarski(A_105, B_104))), inference(resolution, [status(thm)], [c_20, c_345])).
% 11.82/5.01  tff(c_451, plain, (![A_107, B_108, C_109]: (k7_subset_1(A_107, k4_xboole_0(A_107, B_108), C_109)=k4_xboole_0(k4_xboole_0(A_107, B_108), C_109))), inference(resolution, [status(thm)], [c_2, c_423])).
% 11.82/5.01  tff(c_469, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_109)=k4_xboole_0(k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2'), C_109))), inference(superposition, [status(thm), theory('equality')], [c_102, c_451])).
% 11.82/5.01  tff(c_478, plain, (![C_109]: (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_109)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), C_109))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_469])).
% 11.82/5.01  tff(c_16, plain, (![A_19]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.82/5.01  tff(c_69, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, B_63)=B_63 | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.82/5.01  tff(c_78, plain, (![A_19, B_63]: (k9_subset_1(A_19, B_63, B_63)=B_63)), inference(resolution, [status(thm)], [c_16, c_69])).
% 11.82/5.01  tff(c_904, plain, (![A_141, B_142, C_143]: (k9_subset_1(A_141, B_142, k3_subset_1(A_141, C_143))=k7_subset_1(A_141, B_142, C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(A_141)) | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.82/5.01  tff(c_941, plain, (![B_146]: (k9_subset_1(u1_struct_0('#skF_1'), B_146, k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k7_subset_1(u1_struct_0('#skF_1'), B_146, '#skF_2') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_38, c_904])).
% 11.82/5.01  tff(c_955, plain, (k7_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_941])).
% 11.82/5.01  tff(c_959, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_955])).
% 11.82/5.01  tff(c_1318, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_959])).
% 11.82/5.01  tff(c_1442, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1318])).
% 11.82/5.01  tff(c_1449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1442])).
% 11.82/5.01  tff(c_1451, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_959])).
% 11.82/5.01  tff(c_32, plain, (![C_47, A_35, D_49, B_43]: (v3_pre_topc(C_47, A_35) | k1_tops_1(A_35, C_47)!=C_47 | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0(B_43))) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.82/5.01  tff(c_1766, plain, (![D_178, B_179]: (~m1_subset_1(D_178, k1_zfmisc_1(u1_struct_0(B_179))) | ~l1_pre_topc(B_179))), inference(splitLeft, [status(thm)], [c_32])).
% 11.82/5.01  tff(c_1769, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1451, c_1766])).
% 11.82/5.01  tff(c_1787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1769])).
% 11.82/5.01  tff(c_1887, plain, (![C_185, A_186]: (v3_pre_topc(C_185, A_186) | k1_tops_1(A_186, C_185)!=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186))), inference(splitRight, [status(thm)], [c_32])).
% 11.82/5.01  tff(c_1904, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1887])).
% 11.82/5.01  tff(c_1917, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1904])).
% 11.82/5.02  tff(c_1918, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_1917])).
% 11.82/5.02  tff(c_703, plain, (![A_130, B_131]: (m1_subset_1(k2_pre_topc(A_130, B_131), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.82/5.02  tff(c_10, plain, (![A_10, B_11]: (k3_subset_1(A_10, k3_subset_1(A_10, B_11))=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.82/5.02  tff(c_724, plain, (![A_130, B_131]: (k3_subset_1(u1_struct_0(A_130), k3_subset_1(u1_struct_0(A_130), k2_pre_topc(A_130, B_131)))=k2_pre_topc(A_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_703, c_10])).
% 11.82/5.02  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k3_subset_1(A_3, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.82/5.02  tff(c_5158, plain, (![A_259, B_260]: (k4_xboole_0(u1_struct_0(A_259), k2_pre_topc(A_259, B_260))=k3_subset_1(u1_struct_0(A_259), k2_pre_topc(A_259, B_260)) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_703, c_4])).
% 11.82/5.02  tff(c_5170, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_5158])).
% 11.82/5.02  tff(c_5182, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5170])).
% 11.82/5.02  tff(c_129, plain, (![B_71, A_72]: (k4_xboole_0(B_71, A_72)=k3_subset_1(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(resolution, [status(thm)], [c_20, c_91])).
% 11.82/5.02  tff(c_282, plain, (![A_91, B_92]: (k4_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_subset_1(A_91, k4_xboole_0(A_91, B_92)))), inference(resolution, [status(thm)], [c_2, c_129])).
% 11.82/5.02  tff(c_291, plain, (![A_91, B_92]: (r1_tarski(k3_subset_1(A_91, k4_xboole_0(A_91, B_92)), A_91))), inference(superposition, [status(thm), theory('equality')], [c_282, c_2])).
% 11.82/5.02  tff(c_5242, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'))), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5182, c_291])).
% 11.82/5.02  tff(c_5491, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_724, c_5242])).
% 11.82/5.02  tff(c_5510, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_5491])).
% 11.82/5.02  tff(c_355, plain, (![B_21, A_20, C_98]: (k7_subset_1(B_21, A_20, C_98)=k4_xboole_0(A_20, C_98) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_345])).
% 11.82/5.02  tff(c_5536, plain, (![C_264]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_264)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_264))), inference(resolution, [status(thm)], [c_5510, c_355])).
% 11.82/5.02  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.82/5.02  tff(c_124, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_50])).
% 11.82/5.02  tff(c_5550, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5536, c_124])).
% 11.82/5.02  tff(c_5603, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5550, c_2])).
% 11.82/5.02  tff(c_356, plain, (![C_98]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_98)=k4_xboole_0('#skF_2', C_98))), inference(resolution, [status(thm)], [c_38, c_345])).
% 11.82/5.02  tff(c_753, plain, (![A_136, B_137]: (k7_subset_1(u1_struct_0(A_136), B_137, k2_tops_1(A_136, B_137))=k1_tops_1(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.82/5.02  tff(c_763, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_753])).
% 11.82/5.02  tff(c_772, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_356, c_763])).
% 11.82/5.02  tff(c_489, plain, (![B_112, A_113]: (r1_tarski(B_112, k2_pre_topc(A_113, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.82/5.02  tff(c_497, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_489])).
% 11.82/5.02  tff(c_505, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_497])).
% 11.82/5.02  tff(c_513, plain, (![C_98]: (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2', C_98)=k4_xboole_0('#skF_2', C_98))), inference(resolution, [status(thm)], [c_505, c_355])).
% 11.82/5.02  tff(c_101, plain, (![B_21, A_20]: (k4_xboole_0(B_21, A_20)=k3_subset_1(B_21, A_20) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_91])).
% 11.82/5.02  tff(c_514, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_505, c_101])).
% 11.82/5.02  tff(c_5575, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5550, c_514])).
% 11.82/5.02  tff(c_166, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.82/5.02  tff(c_176, plain, (![B_21, A_20]: (k3_subset_1(B_21, k3_subset_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_20, c_166])).
% 11.82/5.02  tff(c_5680, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5575, c_176])).
% 11.82/5.02  tff(c_5705, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_5680])).
% 11.82/5.02  tff(c_5686, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5575, c_6])).
% 11.82/5.02  tff(c_12751, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5686])).
% 11.82/5.02  tff(c_12754, plain, (~r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_12751])).
% 11.82/5.02  tff(c_12758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_505, c_12754])).
% 11.82/5.02  tff(c_12759, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(k2_pre_topc('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_5686])).
% 11.82/5.02  tff(c_4433, plain, (![B_245, B_246, A_247]: (k9_subset_1(B_245, B_246, k3_subset_1(B_245, A_247))=k7_subset_1(B_245, B_246, A_247) | ~m1_subset_1(B_246, k1_zfmisc_1(B_245)) | ~r1_tarski(A_247, B_245))), inference(resolution, [status(thm)], [c_20, c_904])).
% 11.82/5.02  tff(c_13023, plain, (![A_358, B_359, A_360]: (k9_subset_1(A_358, k3_subset_1(A_358, B_359), k3_subset_1(A_358, A_360))=k7_subset_1(A_358, k3_subset_1(A_358, B_359), A_360) | ~r1_tarski(A_360, A_358) | ~m1_subset_1(B_359, k1_zfmisc_1(A_358)))), inference(resolution, [status(thm)], [c_6, c_4433])).
% 11.82/5.02  tff(c_17981, plain, (![A_438, A_439]: (k7_subset_1(A_438, k3_subset_1(A_438, A_439), A_439)=k3_subset_1(A_438, A_439) | ~r1_tarski(A_439, A_438) | ~m1_subset_1(A_439, k1_zfmisc_1(A_438)))), inference(superposition, [status(thm), theory('equality')], [c_13023, c_78])).
% 11.82/5.02  tff(c_17989, plain, (k7_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12759, c_17981])).
% 11.82/5.02  tff(c_18023, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5603, c_772, c_513, c_5705, c_5705, c_17989])).
% 11.82/5.02  tff(c_18025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1918, c_18023])).
% 11.82/5.02  tff(c_18026, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 11.82/5.02  tff(c_18027, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 11.82/5.02  tff(c_34, plain, (![B_43, D_49, C_47, A_35]: (k1_tops_1(B_43, D_49)=D_49 | ~v3_pre_topc(D_49, B_43) | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0(B_43))) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(B_43) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.82/5.02  tff(c_19529, plain, (![C_553, A_554]: (~m1_subset_1(C_553, k1_zfmisc_1(u1_struct_0(A_554))) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554))), inference(splitLeft, [status(thm)], [c_34])).
% 11.82/5.02  tff(c_19543, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_19529])).
% 11.82/5.02  tff(c_19553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_19543])).
% 11.82/5.02  tff(c_19661, plain, (![B_557, D_558]: (k1_tops_1(B_557, D_558)=D_558 | ~v3_pre_topc(D_558, B_557) | ~m1_subset_1(D_558, k1_zfmisc_1(u1_struct_0(B_557))) | ~l1_pre_topc(B_557))), inference(splitRight, [status(thm)], [c_34])).
% 11.82/5.02  tff(c_19678, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_19661])).
% 11.82/5.02  tff(c_19691, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18027, c_19678])).
% 11.82/5.02  tff(c_30, plain, (![A_32, B_34]: (k7_subset_1(u1_struct_0(A_32), k2_pre_topc(A_32, B_34), k1_tops_1(A_32, B_34))=k2_tops_1(A_32, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.82/5.02  tff(c_19706, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19691, c_30])).
% 11.82/5.02  tff(c_19713, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_19706])).
% 11.82/5.02  tff(c_19715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18026, c_19713])).
% 11.82/5.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/5.02  
% 11.82/5.02  Inference rules
% 11.82/5.02  ----------------------
% 11.82/5.02  #Ref     : 0
% 11.82/5.02  #Sup     : 4740
% 11.82/5.02  #Fact    : 0
% 11.82/5.02  #Define  : 0
% 11.82/5.02  #Split   : 13
% 11.82/5.02  #Chain   : 0
% 11.82/5.02  #Close   : 0
% 11.82/5.02  
% 11.82/5.02  Ordering : KBO
% 11.82/5.02  
% 11.82/5.02  Simplification rules
% 11.82/5.02  ----------------------
% 11.82/5.02  #Subsume      : 230
% 11.82/5.02  #Demod        : 5064
% 11.82/5.02  #Tautology    : 2117
% 11.82/5.02  #SimpNegUnit  : 15
% 11.82/5.02  #BackRed      : 32
% 11.82/5.02  
% 11.82/5.02  #Partial instantiations: 0
% 11.82/5.02  #Strategies tried      : 1
% 11.82/5.02  
% 11.82/5.02  Timing (in seconds)
% 11.82/5.02  ----------------------
% 11.82/5.02  Preprocessing        : 0.34
% 11.82/5.02  Parsing              : 0.19
% 11.82/5.02  CNF conversion       : 0.02
% 11.82/5.02  Main loop            : 3.85
% 11.82/5.02  Inferencing          : 0.90
% 11.82/5.02  Reduction            : 1.93
% 11.82/5.02  Demodulation         : 1.61
% 11.82/5.02  BG Simplification    : 0.10
% 11.82/5.02  Subsumption          : 0.69
% 11.82/5.02  Abstraction          : 0.16
% 11.82/5.02  MUC search           : 0.00
% 11.82/5.02  Cooper               : 0.00
% 11.82/5.02  Total                : 4.24
% 11.82/5.02  Index Insertion      : 0.00
% 11.82/5.02  Index Deletion       : 0.00
% 11.82/5.02  Index Matching       : 0.00
% 11.82/5.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
