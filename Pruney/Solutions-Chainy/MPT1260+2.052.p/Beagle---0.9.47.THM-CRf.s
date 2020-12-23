%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:06 EST 2020

% Result     : Theorem 10.33s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 334 expanded)
%              Number of leaves         :   36 ( 128 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 719 expanded)
%              Number of equality atoms :   60 ( 201 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_191,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    ! [C_58,A_46,D_60,B_54] :
      ( v3_pre_topc(C_58,A_46)
      | k1_tops_1(A_46,C_58) != C_58
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0(B_54)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(B_54)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3388,plain,(
    ! [D_180,B_181] :
      ( ~ m1_subset_1(D_180,k1_zfmisc_1(u1_struct_0(B_181)))
      | ~ l1_pre_topc(B_181) ) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_3399,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3388])).

tff(c_3405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3399])).

tff(c_3556,plain,(
    ! [C_184,A_185] :
      ( v3_pre_topc(C_184,A_185)
      | k1_tops_1(A_185,C_184) != C_184
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185) ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3570,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3556])).

tff(c_3576,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3570])).

tff(c_3577,plain,(
    k1_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_3576])).

tff(c_2104,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k2_pre_topc(A_146,B_147),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] :
      ( k7_subset_1(A_22,B_23,C_24) = k4_xboole_0(B_23,C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14537,plain,(
    ! [A_328,B_329,C_330] :
      ( k7_subset_1(u1_struct_0(A_328),k2_pre_topc(A_328,B_329),C_330) = k4_xboole_0(k2_pre_topc(A_328,B_329),C_330)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(resolution,[status(thm)],[c_2104,c_26])).

tff(c_14550,plain,(
    ! [C_330] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_330) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_330)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_14537])).

tff(c_15481,plain,(
    ! [C_334] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_334) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14550])).

tff(c_64,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_115,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_15495,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15481,c_115])).

tff(c_1894,plain,(
    ! [B_143,A_144] :
      ( r1_tarski(B_143,k2_pre_topc(A_144,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1902,plain,
    ( r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1894])).

tff(c_1907,plain,(
    r1_tarski('#skF_2',k2_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1902])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_736,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k3_subset_1(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2733,plain,(
    ! [B_158,A_159] :
      ( k4_xboole_0(B_158,A_159) = k3_subset_1(B_158,A_159)
      | ~ r1_tarski(A_159,B_158) ) ),
    inference(resolution,[status(thm)],[c_36,c_736])).

tff(c_2778,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1907,c_2733])).

tff(c_15520,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15495,c_2778])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1914,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1907,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2772,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_subset_1(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_2733])).

tff(c_2793,plain,(
    ! [A_12,B_13] : k3_subset_1(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2772])).

tff(c_3140,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) = k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2778,c_2793])).

tff(c_3161,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1914,c_2,c_3140])).

tff(c_15587,plain,(
    k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15520,c_3161])).

tff(c_44,plain,(
    ! [A_43,B_45] :
      ( k7_subset_1(u1_struct_0(A_43),k2_pre_topc(A_43,B_45),k1_tops_1(A_43,B_45)) = k2_tops_1(A_43,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_15492,plain,
    ( k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15481,c_44])).

tff(c_15514,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_15492])).

tff(c_15734,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_subset_1(k2_pre_topc('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15514,c_2793])).

tff(c_15759,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15587,c_15734])).

tff(c_1386,plain,(
    ! [A_131,B_132,C_133] :
      ( k7_subset_1(A_131,B_132,C_133) = k4_xboole_0(B_132,C_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1395,plain,(
    ! [C_133] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_133) = k4_xboole_0('#skF_2',C_133) ),
    inference(resolution,[status(thm)],[c_52,c_1386])).

tff(c_2518,plain,(
    ! [A_155,B_156] :
      ( k7_subset_1(u1_struct_0(A_155),B_156,k2_tops_1(A_155,B_156)) = k1_tops_1(A_155,B_156)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2528,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_2518])).

tff(c_2534,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1395,c_2528])).

tff(c_2553,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2534,c_16])).

tff(c_2565,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2553,c_14])).

tff(c_201,plain,(
    ! [A_84,B_85] : k4_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = k3_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_223,plain,(
    ! [A_86,B_87] : r1_tarski(k3_xboole_0(A_86,B_87),A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_16])).

tff(c_245,plain,(
    ! [B_88,A_89] : r1_tarski(k3_xboole_0(B_88,A_89),A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_223])).

tff(c_1161,plain,(
    ! [B_127,A_128] : k3_xboole_0(k3_xboole_0(B_127,A_128),A_128) = k3_xboole_0(B_127,A_128) ),
    inference(resolution,[status(thm)],[c_245,c_14])).

tff(c_1216,plain,(
    ! [A_128,B_127] : k3_xboole_0(A_128,k3_xboole_0(B_127,A_128)) = k3_xboole_0(B_127,A_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_2])).

tff(c_15853,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_15759,c_1216])).

tff(c_15929,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15759,c_2565,c_15853])).

tff(c_15931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3577,c_15929])).

tff(c_15932,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15932,c_115])).

tff(c_16343,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_16429,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16343,c_58])).

tff(c_48,plain,(
    ! [B_54,D_60,C_58,A_46] :
      ( k1_tops_1(B_54,D_60) = D_60
      | ~ v3_pre_topc(D_60,B_54)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0(B_54)))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(B_54)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20026,plain,(
    ! [C_487,A_488] :
      ( ~ m1_subset_1(C_487,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488) ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_20040,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_20026])).

tff(c_20047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_20040])).

tff(c_20178,plain,(
    ! [B_491,D_492] :
      ( k1_tops_1(B_491,D_492) = D_492
      | ~ v3_pre_topc(D_492,B_491)
      | ~ m1_subset_1(D_492,k1_zfmisc_1(u1_struct_0(B_491)))
      | ~ l1_pre_topc(B_491) ) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_20192,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_20178])).

tff(c_20198,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16343,c_20192])).

tff(c_20217,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20198,c_44])).

tff(c_20221,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_20217])).

tff(c_20223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16429,c_20221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.33/3.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.33/3.82  
% 10.33/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.33/3.83  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 10.33/3.83  
% 10.33/3.83  %Foreground sorts:
% 10.33/3.83  
% 10.33/3.83  
% 10.33/3.83  %Background operators:
% 10.33/3.83  
% 10.33/3.83  
% 10.33/3.83  %Foreground operators:
% 10.33/3.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.33/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.33/3.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.33/3.83  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.33/3.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.33/3.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.33/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.33/3.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.33/3.83  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.33/3.83  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.33/3.83  tff('#skF_2', type, '#skF_2': $i).
% 10.33/3.83  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.33/3.83  tff('#skF_1', type, '#skF_1': $i).
% 10.33/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.33/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.33/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.33/3.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.33/3.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.33/3.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.33/3.83  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.33/3.83  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 10.33/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.33/3.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.33/3.83  
% 10.43/3.84  tff(f_148, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 10.43/3.84  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 10.43/3.84  tff(f_86, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.43/3.84  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.43/3.84  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.43/3.84  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.43/3.84  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.43/3.84  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.43/3.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.43/3.84  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.43/3.84  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.43/3.84  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.43/3.84  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 10.43/3.84  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.43/3.84  tff(c_191, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 10.43/3.84  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.43/3.84  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.43/3.84  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.43/3.84  tff(c_46, plain, (![C_58, A_46, D_60, B_54]: (v3_pre_topc(C_58, A_46) | k1_tops_1(A_46, C_58)!=C_58 | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0(B_54))) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(B_54) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.43/3.84  tff(c_3388, plain, (![D_180, B_181]: (~m1_subset_1(D_180, k1_zfmisc_1(u1_struct_0(B_181))) | ~l1_pre_topc(B_181))), inference(splitLeft, [status(thm)], [c_46])).
% 10.43/3.84  tff(c_3399, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3388])).
% 10.43/3.84  tff(c_3405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_3399])).
% 10.43/3.84  tff(c_3556, plain, (![C_184, A_185]: (v3_pre_topc(C_184, A_185) | k1_tops_1(A_185, C_184)!=C_184 | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185))), inference(splitRight, [status(thm)], [c_46])).
% 10.43/3.84  tff(c_3570, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3556])).
% 10.43/3.84  tff(c_3576, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3570])).
% 10.43/3.84  tff(c_3577, plain, (k1_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_191, c_3576])).
% 10.43/3.84  tff(c_2104, plain, (![A_146, B_147]: (m1_subset_1(k2_pre_topc(A_146, B_147), k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.43/3.84  tff(c_26, plain, (![A_22, B_23, C_24]: (k7_subset_1(A_22, B_23, C_24)=k4_xboole_0(B_23, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.43/3.84  tff(c_14537, plain, (![A_328, B_329, C_330]: (k7_subset_1(u1_struct_0(A_328), k2_pre_topc(A_328, B_329), C_330)=k4_xboole_0(k2_pre_topc(A_328, B_329), C_330) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(resolution, [status(thm)], [c_2104, c_26])).
% 10.43/3.84  tff(c_14550, plain, (![C_330]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_330)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_330) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_14537])).
% 10.43/3.84  tff(c_15481, plain, (![C_334]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_334)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_334))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14550])).
% 10.43/3.84  tff(c_64, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.43/3.84  tff(c_115, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_64])).
% 10.43/3.84  tff(c_15495, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15481, c_115])).
% 10.43/3.84  tff(c_1894, plain, (![B_143, A_144]: (r1_tarski(B_143, k2_pre_topc(A_144, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.43/3.84  tff(c_1902, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1894])).
% 10.43/3.84  tff(c_1907, plain, (r1_tarski('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1902])).
% 10.43/3.84  tff(c_36, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.43/3.84  tff(c_736, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k3_subset_1(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.43/3.84  tff(c_2733, plain, (![B_158, A_159]: (k4_xboole_0(B_158, A_159)=k3_subset_1(B_158, A_159) | ~r1_tarski(A_159, B_158))), inference(resolution, [status(thm)], [c_36, c_736])).
% 10.43/3.84  tff(c_2778, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1907, c_2733])).
% 10.43/3.84  tff(c_15520, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15495, c_2778])).
% 10.43/3.84  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.43/3.84  tff(c_1914, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_1907, c_14])).
% 10.43/3.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.43/3.84  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.84  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.43/3.84  tff(c_2772, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_subset_1(A_12, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_16, c_2733])).
% 10.43/3.84  tff(c_2793, plain, (![A_12, B_13]: (k3_subset_1(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2772])).
% 10.43/3.84  tff(c_3140, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))=k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2778, c_2793])).
% 10.43/3.84  tff(c_3161, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1914, c_2, c_3140])).
% 10.43/3.84  tff(c_15587, plain, (k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15520, c_3161])).
% 10.43/3.84  tff(c_44, plain, (![A_43, B_45]: (k7_subset_1(u1_struct_0(A_43), k2_pre_topc(A_43, B_45), k1_tops_1(A_43, B_45))=k2_tops_1(A_43, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.43/3.84  tff(c_15492, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15481, c_44])).
% 10.43/3.84  tff(c_15514, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_15492])).
% 10.43/3.84  tff(c_15734, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_15514, c_2793])).
% 10.43/3.84  tff(c_15759, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15587, c_15734])).
% 10.43/3.84  tff(c_1386, plain, (![A_131, B_132, C_133]: (k7_subset_1(A_131, B_132, C_133)=k4_xboole_0(B_132, C_133) | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.43/3.84  tff(c_1395, plain, (![C_133]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_133)=k4_xboole_0('#skF_2', C_133))), inference(resolution, [status(thm)], [c_52, c_1386])).
% 10.43/3.84  tff(c_2518, plain, (![A_155, B_156]: (k7_subset_1(u1_struct_0(A_155), B_156, k2_tops_1(A_155, B_156))=k1_tops_1(A_155, B_156) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.43/3.84  tff(c_2528, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_2518])).
% 10.43/3.84  tff(c_2534, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1395, c_2528])).
% 10.43/3.84  tff(c_2553, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2534, c_16])).
% 10.43/3.84  tff(c_2565, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2553, c_14])).
% 10.43/3.84  tff(c_201, plain, (![A_84, B_85]: (k4_xboole_0(A_84, k4_xboole_0(A_84, B_85))=k3_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.43/3.84  tff(c_223, plain, (![A_86, B_87]: (r1_tarski(k3_xboole_0(A_86, B_87), A_86))), inference(superposition, [status(thm), theory('equality')], [c_201, c_16])).
% 10.43/3.84  tff(c_245, plain, (![B_88, A_89]: (r1_tarski(k3_xboole_0(B_88, A_89), A_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_223])).
% 10.43/3.84  tff(c_1161, plain, (![B_127, A_128]: (k3_xboole_0(k3_xboole_0(B_127, A_128), A_128)=k3_xboole_0(B_127, A_128))), inference(resolution, [status(thm)], [c_245, c_14])).
% 10.43/3.84  tff(c_1216, plain, (![A_128, B_127]: (k3_xboole_0(A_128, k3_xboole_0(B_127, A_128))=k3_xboole_0(B_127, A_128))), inference(superposition, [status(thm), theory('equality')], [c_1161, c_2])).
% 10.43/3.84  tff(c_15853, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_15759, c_1216])).
% 10.43/3.84  tff(c_15929, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15759, c_2565, c_15853])).
% 10.43/3.84  tff(c_15931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3577, c_15929])).
% 10.43/3.84  tff(c_15932, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 10.43/3.84  tff(c_16342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15932, c_115])).
% 10.43/3.84  tff(c_16343, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_64])).
% 10.43/3.84  tff(c_16429, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16343, c_58])).
% 10.43/3.84  tff(c_48, plain, (![B_54, D_60, C_58, A_46]: (k1_tops_1(B_54, D_60)=D_60 | ~v3_pre_topc(D_60, B_54) | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0(B_54))) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(B_54) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.43/3.84  tff(c_20026, plain, (![C_487, A_488]: (~m1_subset_1(C_487, k1_zfmisc_1(u1_struct_0(A_488))) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488))), inference(splitLeft, [status(thm)], [c_48])).
% 10.43/3.84  tff(c_20040, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_20026])).
% 10.43/3.84  tff(c_20047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_20040])).
% 10.43/3.84  tff(c_20178, plain, (![B_491, D_492]: (k1_tops_1(B_491, D_492)=D_492 | ~v3_pre_topc(D_492, B_491) | ~m1_subset_1(D_492, k1_zfmisc_1(u1_struct_0(B_491))) | ~l1_pre_topc(B_491))), inference(splitRight, [status(thm)], [c_48])).
% 10.43/3.84  tff(c_20192, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_20178])).
% 10.43/3.84  tff(c_20198, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16343, c_20192])).
% 10.43/3.84  tff(c_20217, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20198, c_44])).
% 10.43/3.84  tff(c_20221, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_20217])).
% 10.43/3.84  tff(c_20223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16429, c_20221])).
% 10.43/3.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/3.84  
% 10.43/3.84  Inference rules
% 10.43/3.84  ----------------------
% 10.43/3.84  #Ref     : 0
% 10.43/3.84  #Sup     : 5148
% 10.43/3.84  #Fact    : 0
% 10.43/3.84  #Define  : 0
% 10.43/3.84  #Split   : 12
% 10.43/3.84  #Chain   : 0
% 10.43/3.84  #Close   : 0
% 10.43/3.84  
% 10.43/3.84  Ordering : KBO
% 10.43/3.84  
% 10.43/3.84  Simplification rules
% 10.43/3.84  ----------------------
% 10.43/3.84  #Subsume      : 562
% 10.43/3.84  #Demod        : 4743
% 10.43/3.84  #Tautology    : 2679
% 10.43/3.84  #SimpNegUnit  : 14
% 10.43/3.84  #BackRed      : 27
% 10.43/3.84  
% 10.43/3.84  #Partial instantiations: 0
% 10.43/3.84  #Strategies tried      : 1
% 10.43/3.84  
% 10.43/3.84  Timing (in seconds)
% 10.43/3.84  ----------------------
% 10.43/3.85  Preprocessing        : 0.36
% 10.43/3.85  Parsing              : 0.19
% 10.43/3.85  CNF conversion       : 0.02
% 10.43/3.85  Main loop            : 2.71
% 10.43/3.85  Inferencing          : 0.61
% 10.43/3.85  Reduction            : 1.39
% 10.43/3.85  Demodulation         : 1.19
% 10.43/3.85  BG Simplification    : 0.07
% 10.43/3.85  Subsumption          : 0.49
% 10.43/3.85  Abstraction          : 0.11
% 10.43/3.85  MUC search           : 0.00
% 10.43/3.85  Cooper               : 0.00
% 10.43/3.85  Total                : 3.11
% 10.43/3.85  Index Insertion      : 0.00
% 10.43/3.85  Index Deletion       : 0.00
% 10.43/3.85  Index Matching       : 0.00
% 10.43/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
