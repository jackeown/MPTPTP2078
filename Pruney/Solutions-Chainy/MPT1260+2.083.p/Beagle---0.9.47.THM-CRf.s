%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 377 expanded)
%              Number of leaves         :   39 ( 142 expanded)
%              Depth                    :   14
%              Number of atoms          :  224 ( 850 expanded)
%              Number of equality atoms :   70 ( 202 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_48,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_106,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_229,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,k2_pre_topc(A_85,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_237,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_245,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3')
    | ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_76,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_592,plain,(
    ! [A_114,B_115,C_116] :
      ( k7_subset_1(A_114,k3_subset_1(A_114,B_115),C_116) = k4_xboole_0(k3_subset_1(A_114,B_115),C_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_6,c_178])).

tff(c_606,plain,(
    ! [C_116] : k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_116) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_116) ),
    inference(resolution,[status(thm)],[c_38,c_592])).

tff(c_14,plain,(
    ! [A_12] : m1_subset_1('#skF_1'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,B_64) = B_64
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_12,B_64] : k9_subset_1(A_12,B_64,B_64) = B_64 ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_443,plain,(
    ! [A_106,B_107,C_108] :
      ( k9_subset_1(A_106,B_107,k3_subset_1(A_106,C_108)) = k7_subset_1(A_106,B_107,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_575,plain,(
    ! [B_113] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_113,k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(u1_struct_0('#skF_2'),B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_443])).

tff(c_589,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_575])).

tff(c_781,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_589])).

tff(c_782,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_781])).

tff(c_785,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_782])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_785])).

tff(c_794,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_781])).

tff(c_32,plain,(
    ! [C_45,A_33,D_47,B_41] :
      ( v3_pre_topc(C_45,A_33)
      | k1_tops_1(A_33,C_45) != C_45
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(B_41)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_966,plain,(
    ! [D_142,B_143] :
      ( ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0(B_143)))
      | ~ l1_pre_topc(B_143) ) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_969,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_794,c_966])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_969])).

tff(c_989,plain,(
    ! [C_144,A_145] :
      ( v3_pre_topc(C_144,A_145)
      | k1_tops_1(A_145,C_144) != C_144
      | ~ m1_subset_1(C_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1006,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_989])).

tff(c_1019,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1006])).

tff(c_1020,plain,(
    k1_tops_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1019])).

tff(c_340,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k2_pre_topc(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k7_subset_1(A_14,B_15,C_16) = k4_xboole_0(B_15,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2153,plain,(
    ! [A_189,B_190,C_191] :
      ( k7_subset_1(u1_struct_0(A_189),k2_pre_topc(A_189,B_190),C_191) = k4_xboole_0(k2_pre_topc(A_189,B_190),C_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_340,c_16])).

tff(c_2165,plain,(
    ! [C_191] :
      ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_191) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_191)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_2153])).

tff(c_2179,plain,(
    ! [C_192] : k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),C_192) = k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),C_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2165])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_131,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_50])).

tff(c_2197,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2179,c_131])).

tff(c_107,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_24,A_23] :
      ( k4_xboole_0(B_24,A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_250,plain,(
    k4_xboole_0(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_117])).

tff(c_2226,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2197,c_250])).

tff(c_165,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_175,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_2306,plain,
    ( k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2226,c_175])).

tff(c_2334,plain,(
    k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_2306])).

tff(c_189,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_81) = k4_xboole_0('#skF_3',C_81) ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_378,plain,(
    ! [A_99,B_100] :
      ( k7_subset_1(u1_struct_0(A_99),B_100,k2_tops_1(A_99,B_100)) = k1_tops_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_388,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_378])).

tff(c_397,plain,(
    k4_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k1_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_189,c_388])).

tff(c_316,plain,(
    ! [B_90,A_91,C_92] :
      ( k7_subset_1(B_90,A_91,C_92) = k4_xboole_0(A_91,C_92)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_24,c_178])).

tff(c_325,plain,(
    ! [C_92] : k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',C_92) = k4_xboole_0('#skF_3',C_92) ),
    inference(resolution,[status(thm)],[c_245,c_316])).

tff(c_151,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k3_subset_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k3_subset_1(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_1089,plain,(
    ! [B_151,B_152,A_153] :
      ( k9_subset_1(B_151,B_152,k3_subset_1(B_151,A_153)) = k7_subset_1(B_151,B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(B_151))
      | ~ r1_tarski(A_153,B_151) ) ),
    inference(resolution,[status(thm)],[c_24,c_443])).

tff(c_1270,plain,(
    ! [B_160,A_161,A_162] :
      ( k9_subset_1(B_160,A_161,k3_subset_1(B_160,A_162)) = k7_subset_1(B_160,A_161,A_162)
      | ~ r1_tarski(A_162,B_160)
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(resolution,[status(thm)],[c_24,c_1089])).

tff(c_1419,plain,(
    ! [B_166,A_167] :
      ( k7_subset_1(B_166,k3_subset_1(B_166,A_167),A_167) = k3_subset_1(B_166,A_167)
      | ~ r1_tarski(A_167,B_166)
      | ~ r1_tarski(k3_subset_1(B_166,A_167),B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_96])).

tff(c_1440,plain,(
    ! [A_168,B_169] :
      ( k7_subset_1(A_168,k3_subset_1(A_168,B_169),B_169) = k3_subset_1(A_168,B_169)
      | ~ r1_tarski(B_169,A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(A_168)) ) ),
    inference(resolution,[status(thm)],[c_159,c_1419])).

tff(c_1458,plain,(
    ! [B_24,A_23] :
      ( k7_subset_1(B_24,k3_subset_1(B_24,A_23),A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_1440])).

tff(c_2351,plain,
    ( k7_subset_1(k2_pre_topc('#skF_2','#skF_3'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k3_subset_1(k2_pre_topc('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2334,c_1458])).

tff(c_2384,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2334,c_397,c_325,c_2351])).

tff(c_2385,plain,(
    ~ r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1020,c_2384])).

tff(c_2309,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2226,c_159])).

tff(c_2406,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_pre_topc('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2385,c_2309])).

tff(c_2409,plain,(
    ~ r1_tarski('#skF_3',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_2406])).

tff(c_2413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_2409])).

tff(c_2414,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2415,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2525,plain,(
    ! [A_214,B_215,C_216] :
      ( k7_subset_1(A_214,B_215,C_216) = k4_xboole_0(B_215,C_216)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(A_214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2910,plain,(
    ! [A_248,B_249,C_250] :
      ( k7_subset_1(A_248,k3_subset_1(A_248,B_249),C_250) = k4_xboole_0(k3_subset_1(A_248,B_249),C_250)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(A_248)) ) ),
    inference(resolution,[status(thm)],[c_6,c_2525])).

tff(c_2924,plain,(
    ! [C_250] : k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_250) = k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),C_250) ),
    inference(resolution,[status(thm)],[c_38,c_2910])).

tff(c_2426,plain,(
    ! [A_198,B_199,C_200] :
      ( k9_subset_1(A_198,B_199,B_199) = B_199
      | ~ m1_subset_1(C_200,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2435,plain,(
    ! [A_12,B_199] : k9_subset_1(A_12,B_199,B_199) = B_199 ),
    inference(resolution,[status(thm)],[c_14,c_2426])).

tff(c_2819,plain,(
    ! [A_243,B_244,C_245] :
      ( k9_subset_1(A_243,B_244,k3_subset_1(A_243,C_245)) = k7_subset_1(A_243,B_244,C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(A_243))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(A_243)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3019,plain,(
    ! [B_262] :
      ( k9_subset_1(u1_struct_0('#skF_2'),B_262,k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k7_subset_1(u1_struct_0('#skF_2'),B_262,'#skF_3')
      | ~ m1_subset_1(B_262,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_2819])).

tff(c_3033,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_3019])).

tff(c_3037,plain,
    ( k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_3033])).

tff(c_3205,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3037])).

tff(c_3208,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_3205])).

tff(c_3215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3208])).

tff(c_3217,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3037])).

tff(c_34,plain,(
    ! [B_41,D_47,C_45,A_33] :
      ( k1_tops_1(B_41,D_47) = D_47
      | ~ v3_pre_topc(D_47,B_41)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(B_41)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3295,plain,(
    ! [C_276,A_277] :
      ( ~ m1_subset_1(C_276,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_3298,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3217,c_3295])).

tff(c_3319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3298])).

tff(c_3321,plain,(
    ! [B_278,D_279] :
      ( k1_tops_1(B_278,D_279) = D_279
      | ~ v3_pre_topc(D_279,B_278)
      | ~ m1_subset_1(D_279,k1_zfmisc_1(u1_struct_0(B_278)))
      | ~ l1_pre_topc(B_278) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3338,plain,
    ( k1_tops_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3321])).

tff(c_3351,plain,(
    k1_tops_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2415,c_3338])).

tff(c_30,plain,(
    ! [A_30,B_32] :
      ( k7_subset_1(u1_struct_0(A_30),k2_pre_topc(A_30,B_32),k1_tops_1(A_30,B_32)) = k2_tops_1(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3357,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3351,c_30])).

tff(c_3361,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_3357])).

tff(c_3363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2414,c_3361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:40:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.85  
% 4.65/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.85  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_2 > #skF_3
% 4.65/1.85  
% 4.65/1.85  %Foreground sorts:
% 4.65/1.85  
% 4.65/1.85  
% 4.65/1.85  %Background operators:
% 4.65/1.85  
% 4.65/1.85  
% 4.65/1.85  %Foreground operators:
% 4.65/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.65/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.65/1.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.65/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.65/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.65/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.65/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.65/1.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.65/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.65/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.65/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.65/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.65/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.65/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.65/1.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.65/1.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.65/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.65/1.85  
% 4.65/1.87  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 4.65/1.87  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 4.65/1.87  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.65/1.87  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.65/1.87  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.65/1.87  tff(f_48, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 4.65/1.87  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 4.65/1.87  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 4.65/1.87  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.65/1.87  tff(f_71, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.65/1.87  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.65/1.87  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.65/1.87  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 4.65/1.87  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.65/1.87  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_229, plain, (![B_84, A_85]: (r1_tarski(B_84, k2_pre_topc(A_85, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.65/1.87  tff(c_237, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_229])).
% 4.65/1.87  tff(c_245, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_237])).
% 4.65/1.87  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.65/1.87  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3') | ~v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_76, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.87  tff(c_178, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_592, plain, (![A_114, B_115, C_116]: (k7_subset_1(A_114, k3_subset_1(A_114, B_115), C_116)=k4_xboole_0(k3_subset_1(A_114, B_115), C_116) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(resolution, [status(thm)], [c_6, c_178])).
% 4.65/1.87  tff(c_606, plain, (![C_116]: (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_116)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_116))), inference(resolution, [status(thm)], [c_38, c_592])).
% 4.65/1.87  tff(c_14, plain, (![A_12]: (m1_subset_1('#skF_1'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.65/1.87  tff(c_87, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, B_64)=B_64 | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.87  tff(c_96, plain, (![A_12, B_64]: (k9_subset_1(A_12, B_64, B_64)=B_64)), inference(resolution, [status(thm)], [c_14, c_87])).
% 4.65/1.87  tff(c_443, plain, (![A_106, B_107, C_108]: (k9_subset_1(A_106, B_107, k3_subset_1(A_106, C_108))=k7_subset_1(A_106, B_107, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.87  tff(c_575, plain, (![B_113]: (k9_subset_1(u1_struct_0('#skF_2'), B_113, k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(u1_struct_0('#skF_2'), B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_443])).
% 4.65/1.87  tff(c_589, plain, (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_575])).
% 4.65/1.87  tff(c_781, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_606, c_589])).
% 4.65/1.87  tff(c_782, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_781])).
% 4.65/1.87  tff(c_785, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_782])).
% 4.65/1.87  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_785])).
% 4.65/1.87  tff(c_794, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_781])).
% 4.65/1.87  tff(c_32, plain, (![C_45, A_33, D_47, B_41]: (v3_pre_topc(C_45, A_33) | k1_tops_1(A_33, C_45)!=C_45 | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(B_41))) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(B_41) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.65/1.87  tff(c_966, plain, (![D_142, B_143]: (~m1_subset_1(D_142, k1_zfmisc_1(u1_struct_0(B_143))) | ~l1_pre_topc(B_143))), inference(splitLeft, [status(thm)], [c_32])).
% 4.65/1.87  tff(c_969, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_794, c_966])).
% 4.65/1.87  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_969])).
% 4.65/1.87  tff(c_989, plain, (![C_144, A_145]: (v3_pre_topc(C_144, A_145) | k1_tops_1(A_145, C_144)!=C_144 | ~m1_subset_1(C_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145))), inference(splitRight, [status(thm)], [c_32])).
% 4.65/1.87  tff(c_1006, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_989])).
% 4.65/1.87  tff(c_1019, plain, (v3_pre_topc('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1006])).
% 4.65/1.87  tff(c_1020, plain, (k1_tops_1('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_76, c_1019])).
% 4.65/1.87  tff(c_340, plain, (![A_94, B_95]: (m1_subset_1(k2_pre_topc(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.65/1.87  tff(c_16, plain, (![A_14, B_15, C_16]: (k7_subset_1(A_14, B_15, C_16)=k4_xboole_0(B_15, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_2153, plain, (![A_189, B_190, C_191]: (k7_subset_1(u1_struct_0(A_189), k2_pre_topc(A_189, B_190), C_191)=k4_xboole_0(k2_pre_topc(A_189, B_190), C_191) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_340, c_16])).
% 4.65/1.87  tff(c_2165, plain, (![C_191]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_191)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_191) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_2153])).
% 4.65/1.87  tff(c_2179, plain, (![C_192]: (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), C_192)=k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), C_192))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2165])).
% 4.65/1.87  tff(c_50, plain, (v3_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.65/1.87  tff(c_131, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_76, c_50])).
% 4.65/1.87  tff(c_2197, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2179, c_131])).
% 4.65/1.87  tff(c_107, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.65/1.87  tff(c_117, plain, (![B_24, A_23]: (k4_xboole_0(B_24, A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_107])).
% 4.65/1.87  tff(c_250, plain, (k4_xboole_0(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_245, c_117])).
% 4.65/1.87  tff(c_2226, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2197, c_250])).
% 4.65/1.87  tff(c_165, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.65/1.87  tff(c_175, plain, (![B_24, A_23]: (k3_subset_1(B_24, k3_subset_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_165])).
% 4.65/1.87  tff(c_2306, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2226, c_175])).
% 4.65/1.87  tff(c_2334, plain, (k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_2306])).
% 4.65/1.87  tff(c_189, plain, (![C_81]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_81)=k4_xboole_0('#skF_3', C_81))), inference(resolution, [status(thm)], [c_38, c_178])).
% 4.65/1.87  tff(c_378, plain, (![A_99, B_100]: (k7_subset_1(u1_struct_0(A_99), B_100, k2_tops_1(A_99, B_100))=k1_tops_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.65/1.87  tff(c_388, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_378])).
% 4.65/1.87  tff(c_397, plain, (k4_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k1_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_189, c_388])).
% 4.65/1.87  tff(c_316, plain, (![B_90, A_91, C_92]: (k7_subset_1(B_90, A_91, C_92)=k4_xboole_0(A_91, C_92) | ~r1_tarski(A_91, B_90))), inference(resolution, [status(thm)], [c_24, c_178])).
% 4.65/1.87  tff(c_325, plain, (![C_92]: (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', C_92)=k4_xboole_0('#skF_3', C_92))), inference(resolution, [status(thm)], [c_245, c_316])).
% 4.65/1.87  tff(c_151, plain, (![A_73, B_74]: (m1_subset_1(k3_subset_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.65/1.87  tff(c_22, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.65/1.87  tff(c_159, plain, (![A_73, B_74]: (r1_tarski(k3_subset_1(A_73, B_74), A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_151, c_22])).
% 4.65/1.87  tff(c_1089, plain, (![B_151, B_152, A_153]: (k9_subset_1(B_151, B_152, k3_subset_1(B_151, A_153))=k7_subset_1(B_151, B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(B_151)) | ~r1_tarski(A_153, B_151))), inference(resolution, [status(thm)], [c_24, c_443])).
% 4.65/1.87  tff(c_1270, plain, (![B_160, A_161, A_162]: (k9_subset_1(B_160, A_161, k3_subset_1(B_160, A_162))=k7_subset_1(B_160, A_161, A_162) | ~r1_tarski(A_162, B_160) | ~r1_tarski(A_161, B_160))), inference(resolution, [status(thm)], [c_24, c_1089])).
% 4.65/1.87  tff(c_1419, plain, (![B_166, A_167]: (k7_subset_1(B_166, k3_subset_1(B_166, A_167), A_167)=k3_subset_1(B_166, A_167) | ~r1_tarski(A_167, B_166) | ~r1_tarski(k3_subset_1(B_166, A_167), B_166))), inference(superposition, [status(thm), theory('equality')], [c_1270, c_96])).
% 4.65/1.87  tff(c_1440, plain, (![A_168, B_169]: (k7_subset_1(A_168, k3_subset_1(A_168, B_169), B_169)=k3_subset_1(A_168, B_169) | ~r1_tarski(B_169, A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(A_168)))), inference(resolution, [status(thm)], [c_159, c_1419])).
% 4.65/1.87  tff(c_1458, plain, (![B_24, A_23]: (k7_subset_1(B_24, k3_subset_1(B_24, A_23), A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_1440])).
% 4.65/1.87  tff(c_2351, plain, (k7_subset_1(k2_pre_topc('#skF_2', '#skF_3'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k3_subset_1(k2_pre_topc('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3')) | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2334, c_1458])).
% 4.65/1.87  tff(c_2384, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2334, c_397, c_325, c_2351])).
% 4.65/1.87  tff(c_2385, plain, (~r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1020, c_2384])).
% 4.65/1.87  tff(c_2309, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2226, c_159])).
% 4.65/1.87  tff(c_2406, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_pre_topc('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2385, c_2309])).
% 4.65/1.87  tff(c_2409, plain, (~r1_tarski('#skF_3', k2_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2406])).
% 4.65/1.87  tff(c_2413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_2409])).
% 4.65/1.87  tff(c_2414, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_2415, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.65/1.87  tff(c_2525, plain, (![A_214, B_215, C_216]: (k7_subset_1(A_214, B_215, C_216)=k4_xboole_0(B_215, C_216) | ~m1_subset_1(B_215, k1_zfmisc_1(A_214)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.65/1.87  tff(c_2910, plain, (![A_248, B_249, C_250]: (k7_subset_1(A_248, k3_subset_1(A_248, B_249), C_250)=k4_xboole_0(k3_subset_1(A_248, B_249), C_250) | ~m1_subset_1(B_249, k1_zfmisc_1(A_248)))), inference(resolution, [status(thm)], [c_6, c_2525])).
% 4.65/1.87  tff(c_2924, plain, (![C_250]: (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_250)=k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), C_250))), inference(resolution, [status(thm)], [c_38, c_2910])).
% 4.65/1.87  tff(c_2426, plain, (![A_198, B_199, C_200]: (k9_subset_1(A_198, B_199, B_199)=B_199 | ~m1_subset_1(C_200, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.65/1.87  tff(c_2435, plain, (![A_12, B_199]: (k9_subset_1(A_12, B_199, B_199)=B_199)), inference(resolution, [status(thm)], [c_14, c_2426])).
% 4.65/1.87  tff(c_2819, plain, (![A_243, B_244, C_245]: (k9_subset_1(A_243, B_244, k3_subset_1(A_243, C_245))=k7_subset_1(A_243, B_244, C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(A_243)) | ~m1_subset_1(B_244, k1_zfmisc_1(A_243)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.65/1.87  tff(c_3019, plain, (![B_262]: (k9_subset_1(u1_struct_0('#skF_2'), B_262, k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k7_subset_1(u1_struct_0('#skF_2'), B_262, '#skF_3') | ~m1_subset_1(B_262, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_2819])).
% 4.65/1.87  tff(c_3033, plain, (k7_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2435, c_3019])).
% 4.65/1.87  tff(c_3037, plain, (k4_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_3033])).
% 4.65/1.87  tff(c_3205, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3037])).
% 4.65/1.87  tff(c_3208, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_3205])).
% 4.65/1.87  tff(c_3215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_3208])).
% 4.65/1.87  tff(c_3217, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3037])).
% 4.65/1.87  tff(c_34, plain, (![B_41, D_47, C_45, A_33]: (k1_tops_1(B_41, D_47)=D_47 | ~v3_pre_topc(D_47, B_41) | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(B_41))) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(B_41) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.65/1.87  tff(c_3295, plain, (![C_276, A_277]: (~m1_subset_1(C_276, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277))), inference(splitLeft, [status(thm)], [c_34])).
% 4.65/1.87  tff(c_3298, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3217, c_3295])).
% 4.65/1.87  tff(c_3319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3298])).
% 4.65/1.87  tff(c_3321, plain, (![B_278, D_279]: (k1_tops_1(B_278, D_279)=D_279 | ~v3_pre_topc(D_279, B_278) | ~m1_subset_1(D_279, k1_zfmisc_1(u1_struct_0(B_278))) | ~l1_pre_topc(B_278))), inference(splitRight, [status(thm)], [c_34])).
% 4.65/1.87  tff(c_3338, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3' | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_3321])).
% 4.65/1.87  tff(c_3351, plain, (k1_tops_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2415, c_3338])).
% 4.65/1.87  tff(c_30, plain, (![A_30, B_32]: (k7_subset_1(u1_struct_0(A_30), k2_pre_topc(A_30, B_32), k1_tops_1(A_30, B_32))=k2_tops_1(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.65/1.87  tff(c_3357, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3351, c_30])).
% 4.65/1.87  tff(c_3361, plain, (k7_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_3357])).
% 4.65/1.87  tff(c_3363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2414, c_3361])).
% 4.65/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.87  
% 4.65/1.87  Inference rules
% 4.65/1.87  ----------------------
% 4.65/1.87  #Ref     : 0
% 4.65/1.87  #Sup     : 779
% 4.65/1.87  #Fact    : 0
% 4.65/1.87  #Define  : 0
% 4.65/1.87  #Split   : 9
% 4.65/1.87  #Chain   : 0
% 4.65/1.87  #Close   : 0
% 4.65/1.87  
% 4.65/1.87  Ordering : KBO
% 4.65/1.87  
% 4.65/1.87  Simplification rules
% 4.65/1.87  ----------------------
% 4.65/1.87  #Subsume      : 69
% 4.65/1.87  #Demod        : 475
% 4.65/1.87  #Tautology    : 368
% 4.65/1.87  #SimpNegUnit  : 10
% 4.65/1.87  #BackRed      : 2
% 4.65/1.87  
% 4.65/1.87  #Partial instantiations: 0
% 4.65/1.87  #Strategies tried      : 1
% 4.65/1.87  
% 4.65/1.87  Timing (in seconds)
% 4.65/1.87  ----------------------
% 4.65/1.88  Preprocessing        : 0.33
% 4.65/1.88  Parsing              : 0.18
% 4.65/1.88  CNF conversion       : 0.02
% 4.65/1.88  Main loop            : 0.76
% 4.65/1.88  Inferencing          : 0.29
% 4.65/1.88  Reduction            : 0.25
% 4.65/1.88  Demodulation         : 0.19
% 4.65/1.88  BG Simplification    : 0.04
% 4.65/1.88  Subsumption          : 0.12
% 4.65/1.88  Abstraction          : 0.05
% 4.65/1.88  MUC search           : 0.00
% 4.65/1.88  Cooper               : 0.00
% 4.65/1.88  Total                : 1.14
% 4.65/1.88  Index Insertion      : 0.00
% 4.65/1.88  Index Deletion       : 0.00
% 4.65/1.88  Index Matching       : 0.00
% 4.65/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
