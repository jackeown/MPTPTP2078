%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:27 EST 2020

% Result     : Theorem 9.61s
% Output     : CNFRefutation 9.70s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 265 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 630 expanded)
%              Number of equality atoms :   39 ( 182 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & v4_pre_topc(C,A) )
                 => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_336,plain,(
    ! [A_72,B_73] :
      ( k2_pre_topc(A_72,B_73) = B_73
      | ~ v4_pre_topc(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_350,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_336])).

tff(c_362,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_350])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_121,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),B_57,'#skF_2') = k3_xboole_0(B_57,'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_165,plain,(
    ! [A_63,C_64,B_65] :
      ( k9_subset_1(A_63,C_64,B_65) = k9_subset_1(A_63,B_65,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),B_65,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_65) ),
    inference(resolution,[status(thm)],[c_42,c_165])).

tff(c_179,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_65) = k3_xboole_0(B_65,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_171])).

tff(c_38,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_347,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_336])).

tff(c_359,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_347])).

tff(c_219,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_68) = k3_xboole_0(B_68,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_171])).

tff(c_135,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_121])).

tff(c_226,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_135])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_155,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_34])).

tff(c_288,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_155])).

tff(c_364,plain,(
    k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1','#skF_3')) != k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_288])).

tff(c_366,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),'#skF_2') != k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_364])).

tff(c_418,plain,(
    k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_366])).

tff(c_541,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(k2_pre_topc(A_88,k9_subset_1(u1_struct_0(A_88),B_89,C_90)),k9_subset_1(u1_struct_0(A_88),k2_pre_topc(A_88,B_89),k2_pre_topc(A_88,C_90)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_572,plain,(
    ! [B_57] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_57,'#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',B_57),k2_pre_topc('#skF_1','#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_541])).

tff(c_1719,plain,(
    ! [B_142] :
      ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0(B_142,'#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1',B_142),'#skF_3'))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_135,c_362,c_572])).

tff(c_1750,plain,
    ( r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1719])).

tff(c_1761,plain,(
    r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_226,c_226,c_1750])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1774,plain,
    ( k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_3','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1761,c_2])).

tff(c_1777,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_1774])).

tff(c_74,plain,(
    ! [A_48,B_49] :
      ( k3_subset_1(A_48,k3_subset_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_173,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),B_65,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_65) ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_181,plain,(
    ! [B_65] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_65) = k3_xboole_0(B_65,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_173])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k3_subset_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_425,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,k3_subset_1(A_79,C_81)) = k7_subset_1(A_79,B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1914,plain,(
    ! [A_149,B_150,B_151] :
      ( k9_subset_1(A_149,B_150,k3_subset_1(A_149,k3_subset_1(A_149,B_151))) = k7_subset_1(A_149,B_150,k3_subset_1(A_149,B_151))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(A_149)) ) ),
    inference(resolution,[status(thm)],[c_14,c_425])).

tff(c_2000,plain,(
    ! [B_151] :
      ( k3_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),B_151)),'#skF_3') = k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),B_151))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1914])).

tff(c_8319,plain,(
    ! [B_253] :
      ( k3_xboole_0(k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),B_253)),'#skF_3') = k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),B_253))
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2000])).

tff(c_8378,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_8319])).

tff(c_8409,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_226,c_8378])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k7_subset_1(A_10,B_11,C_12),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_258,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,k2_pre_topc(A_70,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_272,plain,(
    ! [A_70,B_11,C_12] :
      ( r1_tarski(k7_subset_1(u1_struct_0(A_70),B_11,C_12),k2_pre_topc(A_70,k7_subset_1(u1_struct_0(A_70),B_11,C_12)))
      | ~ l1_pre_topc(A_70)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_70))) ) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_8444,plain,
    ( r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_pre_topc('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8409,c_272])).

tff(c_8489,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_8409,c_8444])).

tff(c_8491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1777,c_8489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.61/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.30  
% 9.61/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.61/3.30  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k7_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 9.61/3.30  
% 9.61/3.30  %Foreground sorts:
% 9.61/3.30  
% 9.61/3.30  
% 9.61/3.30  %Background operators:
% 9.61/3.30  
% 9.61/3.30  
% 9.61/3.30  %Foreground operators:
% 9.61/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.61/3.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.61/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.61/3.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.61/3.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.61/3.30  tff('#skF_2', type, '#skF_2': $i).
% 9.61/3.30  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.61/3.30  tff('#skF_3', type, '#skF_3': $i).
% 9.61/3.30  tff('#skF_1', type, '#skF_1': $i).
% 9.61/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.61/3.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.61/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.61/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.61/3.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.61/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.61/3.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.61/3.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.61/3.30  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.61/3.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.61/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.61/3.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.61/3.30  
% 9.70/3.32  tff(f_111, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)) = k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_1)).
% 9.70/3.32  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 9.70/3.32  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.70/3.32  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 9.70/3.32  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 9.70/3.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.70/3.32  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.70/3.32  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.70/3.32  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 9.70/3.32  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 9.70/3.32  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 9.70/3.32  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_36, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_336, plain, (![A_72, B_73]: (k2_pre_topc(A_72, B_73)=B_73 | ~v4_pre_topc(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.70/3.32  tff(c_350, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_336])).
% 9.70/3.32  tff(c_362, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_350])).
% 9.70/3.32  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_121, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.70/3.32  tff(c_134, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), B_57, '#skF_2')=k3_xboole_0(B_57, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_121])).
% 9.70/3.32  tff(c_165, plain, (![A_63, C_64, B_65]: (k9_subset_1(A_63, C_64, B_65)=k9_subset_1(A_63, B_65, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.70/3.32  tff(c_171, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), B_65, '#skF_2')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_65))), inference(resolution, [status(thm)], [c_42, c_165])).
% 9.70/3.32  tff(c_179, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_65)=k3_xboole_0(B_65, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_171])).
% 9.70/3.32  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_347, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_336])).
% 9.70/3.32  tff(c_359, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_347])).
% 9.70/3.32  tff(c_219, plain, (![B_68]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', B_68)=k3_xboole_0(B_68, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_171])).
% 9.70/3.32  tff(c_135, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), B_57, '#skF_3')=k3_xboole_0(B_57, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_121])).
% 9.70/3.32  tff(c_226, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_219, c_135])).
% 9.70/3.32  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.70/3.32  tff(c_155, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_34])).
% 9.70/3.32  tff(c_288, plain, (k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_155])).
% 9.70/3.32  tff(c_364, plain, (k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_pre_topc('#skF_1', '#skF_3'))!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_288])).
% 9.70/3.32  tff(c_366, plain, (k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), '#skF_2')!=k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_364])).
% 9.70/3.32  tff(c_418, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_366])).
% 9.70/3.32  tff(c_541, plain, (![A_88, B_89, C_90]: (r1_tarski(k2_pre_topc(A_88, k9_subset_1(u1_struct_0(A_88), B_89, C_90)), k9_subset_1(u1_struct_0(A_88), k2_pre_topc(A_88, B_89), k2_pre_topc(A_88, C_90))) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.70/3.32  tff(c_572, plain, (![B_57]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_57, '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', B_57), k2_pre_topc('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_541])).
% 9.70/3.32  tff(c_1719, plain, (![B_142]: (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0(B_142, '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', B_142), '#skF_3')) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_135, c_362, c_572])).
% 9.70/3.32  tff(c_1750, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_359, c_1719])).
% 9.70/3.32  tff(c_1761, plain, (r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_226, c_226, c_1750])).
% 9.70/3.32  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.70/3.32  tff(c_1774, plain, (k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_1761, c_2])).
% 9.70/3.32  tff(c_1777, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_418, c_1774])).
% 9.70/3.32  tff(c_74, plain, (![A_48, B_49]: (k3_subset_1(A_48, k3_subset_1(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.70/3.32  tff(c_81, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_74])).
% 9.70/3.32  tff(c_173, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), B_65, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_65))), inference(resolution, [status(thm)], [c_40, c_165])).
% 9.70/3.32  tff(c_181, plain, (![B_65]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_65)=k3_xboole_0(B_65, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_173])).
% 9.70/3.32  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(k3_subset_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.70/3.32  tff(c_425, plain, (![A_79, B_80, C_81]: (k9_subset_1(A_79, B_80, k3_subset_1(A_79, C_81))=k7_subset_1(A_79, B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.70/3.32  tff(c_1914, plain, (![A_149, B_150, B_151]: (k9_subset_1(A_149, B_150, k3_subset_1(A_149, k3_subset_1(A_149, B_151)))=k7_subset_1(A_149, B_150, k3_subset_1(A_149, B_151)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)) | ~m1_subset_1(B_151, k1_zfmisc_1(A_149)))), inference(resolution, [status(thm)], [c_14, c_425])).
% 9.70/3.32  tff(c_2000, plain, (![B_151]: (k3_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), B_151)), '#skF_3')=k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), B_151)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_181, c_1914])).
% 9.70/3.32  tff(c_8319, plain, (![B_253]: (k3_xboole_0(k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), B_253)), '#skF_3')=k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), B_253)) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2000])).
% 9.70/3.32  tff(c_8378, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_81, c_8319])).
% 9.70/3.32  tff(c_8409, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_226, c_8378])).
% 9.70/3.32  tff(c_16, plain, (![A_10, B_11, C_12]: (m1_subset_1(k7_subset_1(A_10, B_11, C_12), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.70/3.32  tff(c_258, plain, (![B_69, A_70]: (r1_tarski(B_69, k2_pre_topc(A_70, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.70/3.32  tff(c_272, plain, (![A_70, B_11, C_12]: (r1_tarski(k7_subset_1(u1_struct_0(A_70), B_11, C_12), k2_pre_topc(A_70, k7_subset_1(u1_struct_0(A_70), B_11, C_12))) | ~l1_pre_topc(A_70) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_70))))), inference(resolution, [status(thm)], [c_16, c_258])).
% 9.70/3.32  tff(c_8444, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_pre_topc('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8409, c_272])).
% 9.70/3.32  tff(c_8489, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_8409, c_8444])).
% 9.70/3.32  tff(c_8491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1777, c_8489])).
% 9.70/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.70/3.32  
% 9.70/3.32  Inference rules
% 9.70/3.32  ----------------------
% 9.70/3.32  #Ref     : 0
% 9.70/3.32  #Sup     : 1976
% 9.70/3.32  #Fact    : 0
% 9.70/3.32  #Define  : 0
% 9.70/3.32  #Split   : 2
% 9.70/3.32  #Chain   : 0
% 9.70/3.32  #Close   : 0
% 9.70/3.32  
% 9.70/3.32  Ordering : KBO
% 9.70/3.32  
% 9.70/3.32  Simplification rules
% 9.70/3.32  ----------------------
% 9.70/3.32  #Subsume      : 33
% 9.70/3.32  #Demod        : 1740
% 9.70/3.32  #Tautology    : 730
% 9.70/3.32  #SimpNegUnit  : 3
% 9.70/3.32  #BackRed      : 20
% 9.70/3.32  
% 9.70/3.32  #Partial instantiations: 0
% 9.70/3.32  #Strategies tried      : 1
% 9.70/3.32  
% 9.70/3.32  Timing (in seconds)
% 9.70/3.32  ----------------------
% 9.70/3.32  Preprocessing        : 0.36
% 9.70/3.32  Parsing              : 0.19
% 9.70/3.32  CNF conversion       : 0.02
% 9.70/3.32  Main loop            : 2.16
% 9.70/3.32  Inferencing          : 0.57
% 9.70/3.32  Reduction            : 1.05
% 9.70/3.32  Demodulation         : 0.89
% 9.70/3.32  BG Simplification    : 0.07
% 9.70/3.32  Subsumption          : 0.36
% 9.70/3.32  Abstraction          : 0.10
% 9.70/3.32  MUC search           : 0.00
% 9.70/3.32  Cooper               : 0.00
% 9.70/3.32  Total                : 2.55
% 9.70/3.32  Index Insertion      : 0.00
% 9.70/3.32  Index Deletion       : 0.00
% 9.70/3.32  Index Matching       : 0.00
% 9.70/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
