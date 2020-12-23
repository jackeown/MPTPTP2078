%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:06 EST 2020

% Result     : Theorem 17.70s
% Output     : CNFRefutation 17.79s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 785 expanded)
%              Number of leaves         :   49 ( 284 expanded)
%              Depth                    :   31
%              Number of atoms          :  332 (1421 expanded)
%              Number of equality atoms :  121 ( 478 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_94,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_155,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_88,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_276,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k2_xboole_0(A_66,B_67)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_149,plain,(
    ! [A_66] : r1_tarski(k1_xboole_0,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_50])).

tff(c_166,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    ! [A_76] : k3_xboole_0(k1_xboole_0,A_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_166])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_76] : k3_xboole_0(A_76,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_392,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_404,plain,(
    ! [A_76] : k5_xboole_0(A_76,k1_xboole_0) = k4_xboole_0(A_76,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_392])).

tff(c_419,plain,(
    ! [A_76] : k5_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_404])).

tff(c_84,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1503,plain,(
    ! [A_151,B_152,C_153] :
      ( k7_subset_1(A_151,B_152,C_153) = k4_xboole_0(B_152,C_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1519,plain,(
    ! [C_153] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_153) = k4_xboole_0('#skF_6',C_153) ),
    inference(resolution,[status(thm)],[c_82,c_1503])).

tff(c_7522,plain,(
    ! [A_320,B_321] :
      ( k7_subset_1(u1_struct_0(A_320),B_321,k2_tops_1(A_320,B_321)) = k1_tops_1(A_320,B_321)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_7538,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_7522])).

tff(c_7548,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1519,c_7538])).

tff(c_1838,plain,(
    ! [A_179,B_180] :
      ( m1_subset_1(k2_pre_topc(A_179,B_180),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_32,B_33,C_34] :
      ( k7_subset_1(A_32,B_33,C_34) = k4_xboole_0(B_33,C_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24114,plain,(
    ! [A_645,B_646,C_647] :
      ( k7_subset_1(u1_struct_0(A_645),k2_pre_topc(A_645,B_646),C_647) = k4_xboole_0(k2_pre_topc(A_645,B_646),C_647)
      | ~ m1_subset_1(B_646,k1_zfmisc_1(u1_struct_0(A_645)))
      | ~ l1_pre_topc(A_645) ) ),
    inference(resolution,[status(thm)],[c_1838,c_62])).

tff(c_24130,plain,(
    ! [C_647] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_647) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_647)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_24114])).

tff(c_24300,plain,(
    ! [C_649] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_649) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_649) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_24130])).

tff(c_24314,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_24300,c_155])).

tff(c_283,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_318,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ r1_tarski(A_85,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_149,c_283])).

tff(c_333,plain,(
    ! [B_22] : k4_xboole_0(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_318])).

tff(c_68,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_511,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_805,plain,(
    ! [B_122,A_123] :
      ( k4_xboole_0(B_122,A_123) = k3_subset_1(B_122,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_68,c_511])).

tff(c_827,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_subset_1(A_21,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_50,c_805])).

tff(c_814,plain,(
    ! [A_66] : k4_xboole_0(A_66,k1_xboole_0) = k3_subset_1(A_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_149,c_805])).

tff(c_830,plain,(
    ! [A_125] : k3_subset_1(A_125,k1_xboole_0) = A_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_814])).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1024,plain,(
    ! [A_132] :
      ( m1_subset_1(A_132,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_132)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_58])).

tff(c_1027,plain,(
    ! [B_38] :
      ( m1_subset_1(B_38,k1_zfmisc_1(B_38))
      | ~ r1_tarski(k1_xboole_0,B_38) ) ),
    inference(resolution,[status(thm)],[c_68,c_1024])).

tff(c_1030,plain,(
    ! [B_38] : m1_subset_1(B_38,k1_zfmisc_1(B_38)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1027])).

tff(c_699,plain,(
    ! [A_113,B_114] :
      ( k3_subset_1(A_113,k3_subset_1(A_113,B_114)) = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_704,plain,(
    ! [B_38,A_37] :
      ( k3_subset_1(B_38,k3_subset_1(B_38,A_37)) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_68,c_699])).

tff(c_836,plain,(
    ! [A_125] :
      ( k3_subset_1(A_125,A_125) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_704])).

tff(c_847,plain,(
    ! [A_126] : k3_subset_1(A_126,A_126) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_836])).

tff(c_859,plain,(
    ! [A_126] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_126))
      | ~ m1_subset_1(A_126,k1_zfmisc_1(A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_58])).

tff(c_1111,plain,(
    ! [A_126] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_859])).

tff(c_1505,plain,(
    ! [A_126,C_153] : k7_subset_1(A_126,k1_xboole_0,C_153) = k4_xboole_0(k1_xboole_0,C_153) ),
    inference(resolution,[status(thm)],[c_1111,c_1503])).

tff(c_1515,plain,(
    ! [A_126,C_153] : k7_subset_1(A_126,k1_xboole_0,C_153) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_1505])).

tff(c_722,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1(k3_subset_1(A_116,B_117),k1_zfmisc_1(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k3_subset_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6667,plain,(
    ! [A_297,B_298] :
      ( k4_xboole_0(A_297,k3_subset_1(A_297,B_298)) = k3_subset_1(A_297,k3_subset_1(A_297,B_298))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(A_297)) ) ),
    inference(resolution,[status(thm)],[c_722,c_56])).

tff(c_18033,plain,(
    ! [B_534,A_535] :
      ( k4_xboole_0(B_534,k3_subset_1(B_534,A_535)) = k3_subset_1(B_534,k3_subset_1(B_534,A_535))
      | ~ r1_tarski(A_535,B_534) ) ),
    inference(resolution,[status(thm)],[c_68,c_6667])).

tff(c_845,plain,(
    ! [A_125] : k3_subset_1(A_125,A_125) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_836])).

tff(c_828,plain,(
    ! [B_16] : k4_xboole_0(B_16,B_16) = k3_subset_1(B_16,B_16) ),
    inference(resolution,[status(thm)],[c_44,c_805])).

tff(c_872,plain,(
    ! [B_16] : k4_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_828])).

tff(c_178,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_44,c_166])).

tff(c_410,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k4_xboole_0(B_16,B_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_392])).

tff(c_874,plain,(
    ! [B_16] : k5_xboole_0(B_16,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_410])).

tff(c_520,plain,(
    ! [A_107,B_108] : k3_xboole_0(k4_xboole_0(A_107,B_108),A_107) = k4_xboole_0(A_107,B_108) ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_46,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_529,plain,(
    ! [A_107,B_108] : k5_xboole_0(k4_xboole_0(A_107,B_108),k4_xboole_0(A_107,B_108)) = k4_xboole_0(k4_xboole_0(A_107,B_108),A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_46])).

tff(c_1946,plain,(
    ! [A_107,B_108] : k4_xboole_0(k4_xboole_0(A_107,B_108),A_107) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_874,c_529])).

tff(c_18337,plain,(
    ! [B_538,A_539] :
      ( k4_xboole_0(k3_subset_1(B_538,k3_subset_1(B_538,A_539)),B_538) = k1_xboole_0
      | ~ r1_tarski(A_539,B_538) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18033,c_1946])).

tff(c_1556,plain,(
    ! [B_159,A_160,C_161] :
      ( k7_subset_1(B_159,A_160,C_161) = k4_xboole_0(A_160,C_161)
      | ~ r1_tarski(A_160,B_159) ) ),
    inference(resolution,[status(thm)],[c_68,c_1503])).

tff(c_1581,plain,(
    ! [A_21,B_22,C_161] : k7_subset_1(A_21,k4_xboole_0(A_21,B_22),C_161) = k4_xboole_0(k4_xboole_0(A_21,B_22),C_161) ),
    inference(resolution,[status(thm)],[c_50,c_1556])).

tff(c_18432,plain,(
    ! [B_538,A_539,C_161] :
      ( k4_xboole_0(k4_xboole_0(k3_subset_1(B_538,k3_subset_1(B_538,A_539)),B_538),C_161) = k7_subset_1(k3_subset_1(B_538,k3_subset_1(B_538,A_539)),k1_xboole_0,C_161)
      | ~ r1_tarski(A_539,B_538) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18337,c_1581])).

tff(c_31618,plain,(
    ! [B_730,A_731,C_732] :
      ( k4_xboole_0(k4_xboole_0(k3_subset_1(B_730,k3_subset_1(B_730,A_731)),B_730),C_732) = k1_xboole_0
      | ~ r1_tarski(A_731,B_730) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1515,c_18432])).

tff(c_31999,plain,(
    ! [A_733,B_734,C_735] :
      ( k4_xboole_0(k4_xboole_0(A_733,B_734),C_735) = k1_xboole_0
      | ~ r1_tarski(A_733,B_734)
      | ~ r1_tarski(A_733,B_734) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_31618])).

tff(c_6689,plain,(
    ! [A_299,B_300,C_301] :
      ( r2_hidden('#skF_3'(A_299,B_300,C_301),A_299)
      | r2_hidden('#skF_4'(A_299,B_300,C_301),C_301)
      | k4_xboole_0(A_299,B_300) = C_301 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_36,plain,(
    ! [A_9,B_10,C_11] :
      ( ~ r2_hidden('#skF_3'(A_9,B_10,C_11),B_10)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6702,plain,(
    ! [A_299,C_301] :
      ( r2_hidden('#skF_4'(A_299,A_299,C_301),C_301)
      | k4_xboole_0(A_299,A_299) = C_301 ) ),
    inference(resolution,[status(thm)],[c_6689,c_36])).

tff(c_6805,plain,(
    ! [A_299,C_301] :
      ( r2_hidden('#skF_4'(A_299,A_299,C_301),C_301)
      | k1_xboole_0 = C_301 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_6702])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19474,plain,(
    ! [D_553,B_554,A_555] :
      ( r2_hidden(D_553,B_554)
      | ~ r2_hidden(D_553,k3_subset_1(B_554,k3_subset_1(B_554,A_555)))
      | ~ r1_tarski(A_555,B_554) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18033,c_26])).

tff(c_19608,plain,(
    ! [D_556,B_557,A_558] :
      ( r2_hidden(D_556,B_557)
      | ~ r2_hidden(D_556,A_558)
      | ~ r1_tarski(A_558,B_557)
      | ~ r1_tarski(A_558,B_557) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_19474])).

tff(c_20228,plain,(
    ! [A_575,C_576,B_577] :
      ( r2_hidden('#skF_4'(A_575,A_575,C_576),B_577)
      | ~ r1_tarski(C_576,B_577)
      | k1_xboole_0 = C_576 ) ),
    inference(resolution,[status(thm)],[c_6805,c_19608])).

tff(c_6831,plain,(
    ! [A_302,C_303] :
      ( r2_hidden('#skF_4'(A_302,A_302,C_303),C_303)
      | k1_xboole_0 = C_303 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_6702])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6901,plain,(
    ! [A_302,A_9,B_10] :
      ( ~ r2_hidden('#skF_4'(A_302,A_302,k4_xboole_0(A_9,B_10)),B_10)
      | k4_xboole_0(A_9,B_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6831,c_24])).

tff(c_20351,plain,(
    ! [A_9,B_577] :
      ( ~ r1_tarski(k4_xboole_0(A_9,B_577),B_577)
      | k4_xboole_0(A_9,B_577) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20228,c_6901])).

tff(c_32066,plain,(
    ! [C_735,A_733,B_734] :
      ( ~ r1_tarski(k1_xboole_0,C_735)
      | k4_xboole_0(k4_xboole_0(A_733,B_734),C_735) = k1_xboole_0
      | ~ r1_tarski(A_733,B_734)
      | ~ r1_tarski(A_733,B_734) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31999,c_20351])).

tff(c_32474,plain,(
    ! [A_736,B_737,C_738] :
      ( k4_xboole_0(k4_xboole_0(A_736,B_737),C_738) = k1_xboole_0
      | ~ r1_tarski(A_736,B_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_32066])).

tff(c_32615,plain,(
    ! [A_736,B_737,C_738,C_161] :
      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(A_736,B_737),C_738),C_161) = k7_subset_1(k4_xboole_0(A_736,B_737),k1_xboole_0,C_161)
      | ~ r1_tarski(A_736,B_737) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32474,c_1581])).

tff(c_37655,plain,(
    ! [A_791,B_792,C_793,C_794] :
      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(A_791,B_792),C_793),C_794) = k1_xboole_0
      | ~ r1_tarski(A_791,B_792) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1515,c_32615])).

tff(c_38186,plain,(
    ! [A_795,C_796,C_797] :
      ( k4_xboole_0(k4_xboole_0(A_795,C_796),C_797) = k1_xboole_0
      | ~ r1_tarski(A_795,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_37655])).

tff(c_40455,plain,(
    ! [A_820,B_821,C_822] :
      ( k4_xboole_0(k3_subset_1(A_820,k4_xboole_0(A_820,B_821)),C_822) = k1_xboole_0
      | ~ r1_tarski(A_820,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_38186])).

tff(c_40989,plain,(
    ! [A_823,B_824] :
      ( k3_subset_1(A_823,k4_xboole_0(A_823,B_824)) = k1_xboole_0
      | ~ r1_tarski(A_823,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40455,c_52])).

tff(c_1296,plain,(
    ! [A_145,B_146] : k4_xboole_0(A_145,k4_xboole_0(A_145,B_146)) = k3_subset_1(A_145,k4_xboole_0(A_145,B_146)) ),
    inference(resolution,[status(thm)],[c_50,c_805])).

tff(c_1327,plain,(
    ! [A_145,B_146] : r1_tarski(k3_subset_1(A_145,k4_xboole_0(A_145,B_146)),A_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_50])).

tff(c_19240,plain,(
    ! [B_547,A_548] :
      ( r1_tarski(k3_subset_1(B_547,k3_subset_1(B_547,k3_subset_1(B_547,A_548))),B_547)
      | ~ r1_tarski(A_548,B_547) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18033,c_1327])).

tff(c_19355,plain,(
    ! [B_549,A_550] :
      ( r1_tarski(k3_subset_1(B_549,A_550),B_549)
      | ~ r1_tarski(A_550,B_549)
      | ~ r1_tarski(A_550,B_549) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_19240])).

tff(c_40,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19413,plain,(
    ! [B_549,A_550] :
      ( k3_subset_1(B_549,A_550) = B_549
      | ~ r1_tarski(B_549,k3_subset_1(B_549,A_550))
      | ~ r1_tarski(A_550,B_549) ) ),
    inference(resolution,[status(thm)],[c_19355,c_40])).

tff(c_41030,plain,(
    ! [A_823,B_824] :
      ( k3_subset_1(A_823,k4_xboole_0(A_823,B_824)) = A_823
      | ~ r1_tarski(A_823,k1_xboole_0)
      | ~ r1_tarski(k4_xboole_0(A_823,B_824),A_823)
      | ~ r1_tarski(A_823,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40989,c_19413])).

tff(c_41536,plain,(
    ! [A_827,B_828] :
      ( k3_subset_1(A_827,k4_xboole_0(A_827,B_828)) = A_827
      | ~ r1_tarski(A_827,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_41030])).

tff(c_1320,plain,(
    ! [D_14,A_145,B_146] :
      ( ~ r2_hidden(D_14,k4_xboole_0(A_145,B_146))
      | ~ r2_hidden(D_14,k3_subset_1(A_145,k4_xboole_0(A_145,B_146))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_24])).

tff(c_43606,plain,(
    ! [D_837,A_838,B_839] :
      ( ~ r2_hidden(D_837,k4_xboole_0(A_838,B_839))
      | ~ r2_hidden(D_837,A_838)
      | ~ r1_tarski(A_838,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41536,c_1320])).

tff(c_44011,plain,(
    ! [D_837] :
      ( ~ r2_hidden(D_837,k1_xboole_0)
      | ~ r2_hidden(D_837,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_43606])).

tff(c_44083,plain,(
    ! [D_837] : ~ r2_hidden(D_837,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_44011])).

tff(c_4256,plain,(
    ! [A_241,B_242,C_243] :
      ( r2_hidden('#skF_1'(A_241,B_242,C_243),B_242)
      | r2_hidden('#skF_2'(A_241,B_242,C_243),C_243)
      | k3_xboole_0(A_241,B_242) = C_243 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_46404,plain,(
    ! [A_872,B_873,A_874,B_875] :
      ( r2_hidden('#skF_2'(A_872,B_873,k4_xboole_0(A_874,B_875)),A_874)
      | r2_hidden('#skF_1'(A_872,B_873,k4_xboole_0(A_874,B_875)),B_873)
      | k4_xboole_0(A_874,B_875) = k3_xboole_0(A_872,B_873) ) ),
    inference(resolution,[status(thm)],[c_4256,c_26])).

tff(c_4372,plain,(
    ! [A_241,B_242,A_9,B_10] :
      ( ~ r2_hidden('#skF_2'(A_241,B_242,k4_xboole_0(A_9,B_10)),B_10)
      | r2_hidden('#skF_1'(A_241,B_242,k4_xboole_0(A_9,B_10)),B_242)
      | k4_xboole_0(A_9,B_10) = k3_xboole_0(A_241,B_242) ) ),
    inference(resolution,[status(thm)],[c_4256,c_24])).

tff(c_46420,plain,(
    ! [A_872,B_873,A_874] :
      ( r2_hidden('#skF_1'(A_872,B_873,k4_xboole_0(A_874,A_874)),B_873)
      | k4_xboole_0(A_874,A_874) = k3_xboole_0(A_872,B_873) ) ),
    inference(resolution,[status(thm)],[c_46404,c_4372])).

tff(c_47059,plain,(
    ! [A_876,B_877] :
      ( r2_hidden('#skF_1'(A_876,B_877,k1_xboole_0),B_877)
      | k3_xboole_0(A_876,B_877) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_872,c_46420])).

tff(c_2779,plain,(
    ! [A_204,B_205,C_206] :
      ( r2_hidden('#skF_1'(A_204,B_205,C_206),A_204)
      | r2_hidden('#skF_2'(A_204,B_205,C_206),C_206)
      | k3_xboole_0(A_204,B_205) = C_206 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2860,plain,(
    ! [A_9,B_10,B_205,C_206] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_9,B_10),B_205,C_206),B_10)
      | r2_hidden('#skF_2'(k4_xboole_0(A_9,B_10),B_205,C_206),C_206)
      | k3_xboole_0(k4_xboole_0(A_9,B_10),B_205) = C_206 ) ),
    inference(resolution,[status(thm)],[c_2779,c_24])).

tff(c_47077,plain,(
    ! [A_9,B_877] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_9,B_877),B_877,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(k4_xboole_0(A_9,B_877),B_877) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_47059,c_2860])).

tff(c_47186,plain,(
    ! [A_9,B_877] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_9,B_877),B_877,k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(B_877,k4_xboole_0(A_9,B_877)) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47077])).

tff(c_47217,plain,(
    ! [B_878,A_879] : k3_xboole_0(B_878,k4_xboole_0(A_879,B_878)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44083,c_47186])).

tff(c_47367,plain,(
    k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24314,c_47217])).

tff(c_48262,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_47367,c_46])).

tff(c_48295,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_7548,c_48262])).

tff(c_294,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_50,c_283])).

tff(c_7625,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7548,c_294])).

tff(c_7650,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_7625])).

tff(c_8046,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7650])).

tff(c_48341,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48295,c_8046])).

tff(c_48372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48341])).

tff(c_48373,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7650])).

tff(c_86,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1688,plain,(
    ! [A_168,B_169] :
      ( v3_pre_topc(k1_tops_1(A_168,B_169),A_168)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1702,plain,
    ( v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1688])).

tff(c_1709,plain,(
    v3_pre_topc(k1_tops_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_1702])).

tff(c_48383,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48373,c_1709])).

tff(c_48391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_48383])).

tff(c_48392,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_48530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_48392])).

tff(c_48531,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_48653,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48531,c_88])).

tff(c_49904,plain,(
    ! [A_991,B_992,C_993] :
      ( k7_subset_1(A_991,B_992,C_993) = k4_xboole_0(B_992,C_993)
      | ~ m1_subset_1(B_992,k1_zfmisc_1(A_991)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_49920,plain,(
    ! [C_993] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_993) = k4_xboole_0('#skF_6',C_993) ),
    inference(resolution,[status(thm)],[c_82,c_49904])).

tff(c_54624,plain,(
    ! [A_1136,B_1137] :
      ( k7_subset_1(u1_struct_0(A_1136),B_1137,k2_tops_1(A_1136,B_1137)) = k1_tops_1(A_1136,B_1137)
      | ~ m1_subset_1(B_1137,k1_zfmisc_1(u1_struct_0(A_1136)))
      | ~ l1_pre_topc(A_1136) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54640,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_54624])).

tff(c_54650,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_49920,c_54640])).

tff(c_48661,plain,(
    ! [B_914,A_915] :
      ( B_914 = A_915
      | ~ r1_tarski(B_914,A_915)
      | ~ r1_tarski(A_915,B_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48672,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_50,c_48661])).

tff(c_54727,plain,
    ( k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54650,c_48672])).

tff(c_54757,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54650,c_54727])).

tff(c_55192,plain,(
    ~ r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54757])).

tff(c_57486,plain,(
    ! [B_1195,A_1196,C_1197] :
      ( r1_tarski(B_1195,k1_tops_1(A_1196,C_1197))
      | ~ r1_tarski(B_1195,C_1197)
      | ~ v3_pre_topc(B_1195,A_1196)
      | ~ m1_subset_1(C_1197,k1_zfmisc_1(u1_struct_0(A_1196)))
      | ~ m1_subset_1(B_1195,k1_zfmisc_1(u1_struct_0(A_1196)))
      | ~ l1_pre_topc(A_1196) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_57502,plain,(
    ! [B_1195] :
      ( r1_tarski(B_1195,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_1195,'#skF_6')
      | ~ v3_pre_topc(B_1195,'#skF_5')
      | ~ m1_subset_1(B_1195,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_57486])).

tff(c_57612,plain,(
    ! [B_1201] :
      ( r1_tarski(B_1201,k1_tops_1('#skF_5','#skF_6'))
      | ~ r1_tarski(B_1201,'#skF_6')
      | ~ v3_pre_topc(B_1201,'#skF_5')
      | ~ m1_subset_1(B_1201,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_57502])).

tff(c_57635,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_57612])).

tff(c_57647,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48531,c_44,c_57635])).

tff(c_57649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55192,c_57647])).

tff(c_57650,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54757])).

tff(c_74,plain,(
    ! [A_43,B_45] :
      ( k7_subset_1(u1_struct_0(A_43),k2_pre_topc(A_43,B_45),k1_tops_1(A_43,B_45)) = k2_tops_1(A_43,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57671,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_57650,c_74])).

tff(c_57678,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_57671])).

tff(c_57680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48653,c_57678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.70/9.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.79/9.20  
% 17.79/9.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.79/9.20  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 17.79/9.20  
% 17.79/9.20  %Foreground sorts:
% 17.79/9.20  
% 17.79/9.20  
% 17.79/9.20  %Background operators:
% 17.79/9.20  
% 17.79/9.20  
% 17.79/9.20  %Foreground operators:
% 17.79/9.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.79/9.20  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 17.79/9.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.79/9.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.79/9.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.79/9.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 17.79/9.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.79/9.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.79/9.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.79/9.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.79/9.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.79/9.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.79/9.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.79/9.20  tff('#skF_5', type, '#skF_5': $i).
% 17.79/9.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 17.79/9.20  tff('#skF_6', type, '#skF_6': $i).
% 17.79/9.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 17.79/9.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.79/9.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.79/9.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.79/9.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.79/9.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.79/9.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.79/9.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.79/9.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.79/9.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.79/9.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 17.79/9.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.79/9.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.79/9.20  
% 17.79/9.23  tff(f_147, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 17.79/9.23  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.79/9.23  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 17.79/9.23  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 17.79/9.23  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.79/9.23  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.79/9.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.79/9.23  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.79/9.23  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 17.79/9.23  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 17.79/9.23  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 17.79/9.23  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.79/9.23  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.79/9.23  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 17.79/9.23  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.79/9.23  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.79/9.23  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 17.79/9.23  tff(f_100, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 17.79/9.23  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 17.79/9.23  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 17.79/9.23  tff(c_94, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.79/9.23  tff(c_155, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_94])).
% 17.79/9.23  tff(c_88, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.79/9.23  tff(c_276, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_88])).
% 17.79/9.23  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.79/9.23  tff(c_52, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 17.79/9.23  tff(c_144, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k2_xboole_0(A_66, B_67))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.79/9.23  tff(c_50, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.79/9.23  tff(c_149, plain, (![A_66]: (r1_tarski(k1_xboole_0, A_66))), inference(superposition, [status(thm), theory('equality')], [c_144, c_50])).
% 17.79/9.23  tff(c_166, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 17.79/9.23  tff(c_188, plain, (![A_76]: (k3_xboole_0(k1_xboole_0, A_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_149, c_166])).
% 17.79/9.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.79/9.23  tff(c_197, plain, (![A_76]: (k3_xboole_0(A_76, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 17.79/9.23  tff(c_392, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.79/9.23  tff(c_404, plain, (![A_76]: (k5_xboole_0(A_76, k1_xboole_0)=k4_xboole_0(A_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_197, c_392])).
% 17.79/9.23  tff(c_419, plain, (![A_76]: (k5_xboole_0(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_404])).
% 17.79/9.23  tff(c_84, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.79/9.23  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.79/9.23  tff(c_1503, plain, (![A_151, B_152, C_153]: (k7_subset_1(A_151, B_152, C_153)=k4_xboole_0(B_152, C_153) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.79/9.23  tff(c_1519, plain, (![C_153]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_153)=k4_xboole_0('#skF_6', C_153))), inference(resolution, [status(thm)], [c_82, c_1503])).
% 17.79/9.23  tff(c_7522, plain, (![A_320, B_321]: (k7_subset_1(u1_struct_0(A_320), B_321, k2_tops_1(A_320, B_321))=k1_tops_1(A_320, B_321) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_320))) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_135])).
% 17.79/9.23  tff(c_7538, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_82, c_7522])).
% 17.79/9.23  tff(c_7548, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1519, c_7538])).
% 17.79/9.23  tff(c_1838, plain, (![A_179, B_180]: (m1_subset_1(k2_pre_topc(A_179, B_180), k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.79/9.23  tff(c_62, plain, (![A_32, B_33, C_34]: (k7_subset_1(A_32, B_33, C_34)=k4_xboole_0(B_33, C_34) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.79/9.23  tff(c_24114, plain, (![A_645, B_646, C_647]: (k7_subset_1(u1_struct_0(A_645), k2_pre_topc(A_645, B_646), C_647)=k4_xboole_0(k2_pre_topc(A_645, B_646), C_647) | ~m1_subset_1(B_646, k1_zfmisc_1(u1_struct_0(A_645))) | ~l1_pre_topc(A_645))), inference(resolution, [status(thm)], [c_1838, c_62])).
% 17.79/9.23  tff(c_24130, plain, (![C_647]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_647)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_647) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_24114])).
% 17.79/9.23  tff(c_24300, plain, (![C_649]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_649)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_649))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_24130])).
% 17.79/9.23  tff(c_24314, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_24300, c_155])).
% 17.79/9.23  tff(c_283, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.79/9.23  tff(c_318, plain, (![A_85]: (k1_xboole_0=A_85 | ~r1_tarski(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_149, c_283])).
% 17.79/9.23  tff(c_333, plain, (![B_22]: (k4_xboole_0(k1_xboole_0, B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_318])).
% 17.79/9.23  tff(c_68, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_86])).
% 17.79/9.23  tff(c_511, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.79/9.23  tff(c_805, plain, (![B_122, A_123]: (k4_xboole_0(B_122, A_123)=k3_subset_1(B_122, A_123) | ~r1_tarski(A_123, B_122))), inference(resolution, [status(thm)], [c_68, c_511])).
% 17.79/9.23  tff(c_827, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_subset_1(A_21, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_50, c_805])).
% 17.79/9.23  tff(c_814, plain, (![A_66]: (k4_xboole_0(A_66, k1_xboole_0)=k3_subset_1(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_149, c_805])).
% 17.79/9.23  tff(c_830, plain, (![A_125]: (k3_subset_1(A_125, k1_xboole_0)=A_125)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_814])).
% 17.79/9.23  tff(c_58, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.79/9.23  tff(c_1024, plain, (![A_132]: (m1_subset_1(A_132, k1_zfmisc_1(A_132)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_132)))), inference(superposition, [status(thm), theory('equality')], [c_830, c_58])).
% 17.79/9.23  tff(c_1027, plain, (![B_38]: (m1_subset_1(B_38, k1_zfmisc_1(B_38)) | ~r1_tarski(k1_xboole_0, B_38))), inference(resolution, [status(thm)], [c_68, c_1024])).
% 17.79/9.23  tff(c_1030, plain, (![B_38]: (m1_subset_1(B_38, k1_zfmisc_1(B_38)))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1027])).
% 17.79/9.23  tff(c_699, plain, (![A_113, B_114]: (k3_subset_1(A_113, k3_subset_1(A_113, B_114))=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.79/9.23  tff(c_704, plain, (![B_38, A_37]: (k3_subset_1(B_38, k3_subset_1(B_38, A_37))=A_37 | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_68, c_699])).
% 17.79/9.23  tff(c_836, plain, (![A_125]: (k3_subset_1(A_125, A_125)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_125))), inference(superposition, [status(thm), theory('equality')], [c_830, c_704])).
% 17.79/9.23  tff(c_847, plain, (![A_126]: (k3_subset_1(A_126, A_126)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_836])).
% 17.79/9.23  tff(c_859, plain, (![A_126]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_126)) | ~m1_subset_1(A_126, k1_zfmisc_1(A_126)))), inference(superposition, [status(thm), theory('equality')], [c_847, c_58])).
% 17.79/9.23  tff(c_1111, plain, (![A_126]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_126)))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_859])).
% 17.79/9.23  tff(c_1505, plain, (![A_126, C_153]: (k7_subset_1(A_126, k1_xboole_0, C_153)=k4_xboole_0(k1_xboole_0, C_153))), inference(resolution, [status(thm)], [c_1111, c_1503])).
% 17.79/9.23  tff(c_1515, plain, (![A_126, C_153]: (k7_subset_1(A_126, k1_xboole_0, C_153)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_333, c_1505])).
% 17.79/9.23  tff(c_722, plain, (![A_116, B_117]: (m1_subset_1(k3_subset_1(A_116, B_117), k1_zfmisc_1(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.79/9.23  tff(c_56, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k3_subset_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 17.79/9.23  tff(c_6667, plain, (![A_297, B_298]: (k4_xboole_0(A_297, k3_subset_1(A_297, B_298))=k3_subset_1(A_297, k3_subset_1(A_297, B_298)) | ~m1_subset_1(B_298, k1_zfmisc_1(A_297)))), inference(resolution, [status(thm)], [c_722, c_56])).
% 17.79/9.23  tff(c_18033, plain, (![B_534, A_535]: (k4_xboole_0(B_534, k3_subset_1(B_534, A_535))=k3_subset_1(B_534, k3_subset_1(B_534, A_535)) | ~r1_tarski(A_535, B_534))), inference(resolution, [status(thm)], [c_68, c_6667])).
% 17.79/9.23  tff(c_845, plain, (![A_125]: (k3_subset_1(A_125, A_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_836])).
% 17.79/9.23  tff(c_828, plain, (![B_16]: (k4_xboole_0(B_16, B_16)=k3_subset_1(B_16, B_16))), inference(resolution, [status(thm)], [c_44, c_805])).
% 17.79/9.23  tff(c_872, plain, (![B_16]: (k4_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_845, c_828])).
% 17.79/9.23  tff(c_178, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_44, c_166])).
% 17.79/9.23  tff(c_410, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k4_xboole_0(B_16, B_16))), inference(superposition, [status(thm), theory('equality')], [c_178, c_392])).
% 17.79/9.23  tff(c_874, plain, (![B_16]: (k5_xboole_0(B_16, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_872, c_410])).
% 17.79/9.23  tff(c_520, plain, (![A_107, B_108]: (k3_xboole_0(k4_xboole_0(A_107, B_108), A_107)=k4_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_50, c_166])).
% 17.79/9.23  tff(c_46, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.79/9.23  tff(c_529, plain, (![A_107, B_108]: (k5_xboole_0(k4_xboole_0(A_107, B_108), k4_xboole_0(A_107, B_108))=k4_xboole_0(k4_xboole_0(A_107, B_108), A_107))), inference(superposition, [status(thm), theory('equality')], [c_520, c_46])).
% 17.79/9.23  tff(c_1946, plain, (![A_107, B_108]: (k4_xboole_0(k4_xboole_0(A_107, B_108), A_107)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_874, c_529])).
% 17.79/9.23  tff(c_18337, plain, (![B_538, A_539]: (k4_xboole_0(k3_subset_1(B_538, k3_subset_1(B_538, A_539)), B_538)=k1_xboole_0 | ~r1_tarski(A_539, B_538))), inference(superposition, [status(thm), theory('equality')], [c_18033, c_1946])).
% 17.79/9.23  tff(c_1556, plain, (![B_159, A_160, C_161]: (k7_subset_1(B_159, A_160, C_161)=k4_xboole_0(A_160, C_161) | ~r1_tarski(A_160, B_159))), inference(resolution, [status(thm)], [c_68, c_1503])).
% 17.79/9.23  tff(c_1581, plain, (![A_21, B_22, C_161]: (k7_subset_1(A_21, k4_xboole_0(A_21, B_22), C_161)=k4_xboole_0(k4_xboole_0(A_21, B_22), C_161))), inference(resolution, [status(thm)], [c_50, c_1556])).
% 17.79/9.23  tff(c_18432, plain, (![B_538, A_539, C_161]: (k4_xboole_0(k4_xboole_0(k3_subset_1(B_538, k3_subset_1(B_538, A_539)), B_538), C_161)=k7_subset_1(k3_subset_1(B_538, k3_subset_1(B_538, A_539)), k1_xboole_0, C_161) | ~r1_tarski(A_539, B_538))), inference(superposition, [status(thm), theory('equality')], [c_18337, c_1581])).
% 17.79/9.23  tff(c_31618, plain, (![B_730, A_731, C_732]: (k4_xboole_0(k4_xboole_0(k3_subset_1(B_730, k3_subset_1(B_730, A_731)), B_730), C_732)=k1_xboole_0 | ~r1_tarski(A_731, B_730))), inference(demodulation, [status(thm), theory('equality')], [c_1515, c_18432])).
% 17.79/9.23  tff(c_31999, plain, (![A_733, B_734, C_735]: (k4_xboole_0(k4_xboole_0(A_733, B_734), C_735)=k1_xboole_0 | ~r1_tarski(A_733, B_734) | ~r1_tarski(A_733, B_734))), inference(superposition, [status(thm), theory('equality')], [c_704, c_31618])).
% 17.79/9.23  tff(c_6689, plain, (![A_299, B_300, C_301]: (r2_hidden('#skF_3'(A_299, B_300, C_301), A_299) | r2_hidden('#skF_4'(A_299, B_300, C_301), C_301) | k4_xboole_0(A_299, B_300)=C_301)), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.79/9.23  tff(c_36, plain, (![A_9, B_10, C_11]: (~r2_hidden('#skF_3'(A_9, B_10, C_11), B_10) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.79/9.23  tff(c_6702, plain, (![A_299, C_301]: (r2_hidden('#skF_4'(A_299, A_299, C_301), C_301) | k4_xboole_0(A_299, A_299)=C_301)), inference(resolution, [status(thm)], [c_6689, c_36])).
% 17.79/9.23  tff(c_6805, plain, (![A_299, C_301]: (r2_hidden('#skF_4'(A_299, A_299, C_301), C_301) | k1_xboole_0=C_301)), inference(demodulation, [status(thm), theory('equality')], [c_872, c_6702])).
% 17.79/9.23  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.79/9.23  tff(c_19474, plain, (![D_553, B_554, A_555]: (r2_hidden(D_553, B_554) | ~r2_hidden(D_553, k3_subset_1(B_554, k3_subset_1(B_554, A_555))) | ~r1_tarski(A_555, B_554))), inference(superposition, [status(thm), theory('equality')], [c_18033, c_26])).
% 17.79/9.23  tff(c_19608, plain, (![D_556, B_557, A_558]: (r2_hidden(D_556, B_557) | ~r2_hidden(D_556, A_558) | ~r1_tarski(A_558, B_557) | ~r1_tarski(A_558, B_557))), inference(superposition, [status(thm), theory('equality')], [c_704, c_19474])).
% 17.79/9.23  tff(c_20228, plain, (![A_575, C_576, B_577]: (r2_hidden('#skF_4'(A_575, A_575, C_576), B_577) | ~r1_tarski(C_576, B_577) | k1_xboole_0=C_576)), inference(resolution, [status(thm)], [c_6805, c_19608])).
% 17.79/9.23  tff(c_6831, plain, (![A_302, C_303]: (r2_hidden('#skF_4'(A_302, A_302, C_303), C_303) | k1_xboole_0=C_303)), inference(demodulation, [status(thm), theory('equality')], [c_872, c_6702])).
% 17.79/9.23  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.79/9.23  tff(c_6901, plain, (![A_302, A_9, B_10]: (~r2_hidden('#skF_4'(A_302, A_302, k4_xboole_0(A_9, B_10)), B_10) | k4_xboole_0(A_9, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6831, c_24])).
% 17.79/9.23  tff(c_20351, plain, (![A_9, B_577]: (~r1_tarski(k4_xboole_0(A_9, B_577), B_577) | k4_xboole_0(A_9, B_577)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20228, c_6901])).
% 17.79/9.23  tff(c_32066, plain, (![C_735, A_733, B_734]: (~r1_tarski(k1_xboole_0, C_735) | k4_xboole_0(k4_xboole_0(A_733, B_734), C_735)=k1_xboole_0 | ~r1_tarski(A_733, B_734) | ~r1_tarski(A_733, B_734))), inference(superposition, [status(thm), theory('equality')], [c_31999, c_20351])).
% 17.79/9.23  tff(c_32474, plain, (![A_736, B_737, C_738]: (k4_xboole_0(k4_xboole_0(A_736, B_737), C_738)=k1_xboole_0 | ~r1_tarski(A_736, B_737))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_32066])).
% 17.79/9.23  tff(c_32615, plain, (![A_736, B_737, C_738, C_161]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_736, B_737), C_738), C_161)=k7_subset_1(k4_xboole_0(A_736, B_737), k1_xboole_0, C_161) | ~r1_tarski(A_736, B_737))), inference(superposition, [status(thm), theory('equality')], [c_32474, c_1581])).
% 17.79/9.23  tff(c_37655, plain, (![A_791, B_792, C_793, C_794]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(A_791, B_792), C_793), C_794)=k1_xboole_0 | ~r1_tarski(A_791, B_792))), inference(demodulation, [status(thm), theory('equality')], [c_1515, c_32615])).
% 17.79/9.23  tff(c_38186, plain, (![A_795, C_796, C_797]: (k4_xboole_0(k4_xboole_0(A_795, C_796), C_797)=k1_xboole_0 | ~r1_tarski(A_795, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_37655])).
% 17.79/9.23  tff(c_40455, plain, (![A_820, B_821, C_822]: (k4_xboole_0(k3_subset_1(A_820, k4_xboole_0(A_820, B_821)), C_822)=k1_xboole_0 | ~r1_tarski(A_820, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_827, c_38186])).
% 17.79/9.23  tff(c_40989, plain, (![A_823, B_824]: (k3_subset_1(A_823, k4_xboole_0(A_823, B_824))=k1_xboole_0 | ~r1_tarski(A_823, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40455, c_52])).
% 17.79/9.23  tff(c_1296, plain, (![A_145, B_146]: (k4_xboole_0(A_145, k4_xboole_0(A_145, B_146))=k3_subset_1(A_145, k4_xboole_0(A_145, B_146)))), inference(resolution, [status(thm)], [c_50, c_805])).
% 17.79/9.23  tff(c_1327, plain, (![A_145, B_146]: (r1_tarski(k3_subset_1(A_145, k4_xboole_0(A_145, B_146)), A_145))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_50])).
% 17.79/9.23  tff(c_19240, plain, (![B_547, A_548]: (r1_tarski(k3_subset_1(B_547, k3_subset_1(B_547, k3_subset_1(B_547, A_548))), B_547) | ~r1_tarski(A_548, B_547))), inference(superposition, [status(thm), theory('equality')], [c_18033, c_1327])).
% 17.79/9.23  tff(c_19355, plain, (![B_549, A_550]: (r1_tarski(k3_subset_1(B_549, A_550), B_549) | ~r1_tarski(A_550, B_549) | ~r1_tarski(A_550, B_549))), inference(superposition, [status(thm), theory('equality')], [c_704, c_19240])).
% 17.79/9.23  tff(c_40, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.79/9.23  tff(c_19413, plain, (![B_549, A_550]: (k3_subset_1(B_549, A_550)=B_549 | ~r1_tarski(B_549, k3_subset_1(B_549, A_550)) | ~r1_tarski(A_550, B_549))), inference(resolution, [status(thm)], [c_19355, c_40])).
% 17.79/9.23  tff(c_41030, plain, (![A_823, B_824]: (k3_subset_1(A_823, k4_xboole_0(A_823, B_824))=A_823 | ~r1_tarski(A_823, k1_xboole_0) | ~r1_tarski(k4_xboole_0(A_823, B_824), A_823) | ~r1_tarski(A_823, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40989, c_19413])).
% 17.79/9.23  tff(c_41536, plain, (![A_827, B_828]: (k3_subset_1(A_827, k4_xboole_0(A_827, B_828))=A_827 | ~r1_tarski(A_827, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_41030])).
% 17.79/9.23  tff(c_1320, plain, (![D_14, A_145, B_146]: (~r2_hidden(D_14, k4_xboole_0(A_145, B_146)) | ~r2_hidden(D_14, k3_subset_1(A_145, k4_xboole_0(A_145, B_146))))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_24])).
% 17.79/9.23  tff(c_43606, plain, (![D_837, A_838, B_839]: (~r2_hidden(D_837, k4_xboole_0(A_838, B_839)) | ~r2_hidden(D_837, A_838) | ~r1_tarski(A_838, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_41536, c_1320])).
% 17.79/9.23  tff(c_44011, plain, (![D_837]: (~r2_hidden(D_837, k1_xboole_0) | ~r2_hidden(D_837, k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_333, c_43606])).
% 17.79/9.23  tff(c_44083, plain, (![D_837]: (~r2_hidden(D_837, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_44011])).
% 17.79/9.23  tff(c_4256, plain, (![A_241, B_242, C_243]: (r2_hidden('#skF_1'(A_241, B_242, C_243), B_242) | r2_hidden('#skF_2'(A_241, B_242, C_243), C_243) | k3_xboole_0(A_241, B_242)=C_243)), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.79/9.23  tff(c_46404, plain, (![A_872, B_873, A_874, B_875]: (r2_hidden('#skF_2'(A_872, B_873, k4_xboole_0(A_874, B_875)), A_874) | r2_hidden('#skF_1'(A_872, B_873, k4_xboole_0(A_874, B_875)), B_873) | k4_xboole_0(A_874, B_875)=k3_xboole_0(A_872, B_873))), inference(resolution, [status(thm)], [c_4256, c_26])).
% 17.79/9.23  tff(c_4372, plain, (![A_241, B_242, A_9, B_10]: (~r2_hidden('#skF_2'(A_241, B_242, k4_xboole_0(A_9, B_10)), B_10) | r2_hidden('#skF_1'(A_241, B_242, k4_xboole_0(A_9, B_10)), B_242) | k4_xboole_0(A_9, B_10)=k3_xboole_0(A_241, B_242))), inference(resolution, [status(thm)], [c_4256, c_24])).
% 17.79/9.23  tff(c_46420, plain, (![A_872, B_873, A_874]: (r2_hidden('#skF_1'(A_872, B_873, k4_xboole_0(A_874, A_874)), B_873) | k4_xboole_0(A_874, A_874)=k3_xboole_0(A_872, B_873))), inference(resolution, [status(thm)], [c_46404, c_4372])).
% 17.79/9.23  tff(c_47059, plain, (![A_876, B_877]: (r2_hidden('#skF_1'(A_876, B_877, k1_xboole_0), B_877) | k3_xboole_0(A_876, B_877)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_872, c_872, c_46420])).
% 17.79/9.23  tff(c_2779, plain, (![A_204, B_205, C_206]: (r2_hidden('#skF_1'(A_204, B_205, C_206), A_204) | r2_hidden('#skF_2'(A_204, B_205, C_206), C_206) | k3_xboole_0(A_204, B_205)=C_206)), inference(cnfTransformation, [status(thm)], [f_36])).
% 17.79/9.23  tff(c_2860, plain, (![A_9, B_10, B_205, C_206]: (~r2_hidden('#skF_1'(k4_xboole_0(A_9, B_10), B_205, C_206), B_10) | r2_hidden('#skF_2'(k4_xboole_0(A_9, B_10), B_205, C_206), C_206) | k3_xboole_0(k4_xboole_0(A_9, B_10), B_205)=C_206)), inference(resolution, [status(thm)], [c_2779, c_24])).
% 17.79/9.23  tff(c_47077, plain, (![A_9, B_877]: (r2_hidden('#skF_2'(k4_xboole_0(A_9, B_877), B_877, k1_xboole_0), k1_xboole_0) | k3_xboole_0(k4_xboole_0(A_9, B_877), B_877)=k1_xboole_0)), inference(resolution, [status(thm)], [c_47059, c_2860])).
% 17.79/9.23  tff(c_47186, plain, (![A_9, B_877]: (r2_hidden('#skF_2'(k4_xboole_0(A_9, B_877), B_877, k1_xboole_0), k1_xboole_0) | k3_xboole_0(B_877, k4_xboole_0(A_9, B_877))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47077])).
% 17.79/9.23  tff(c_47217, plain, (![B_878, A_879]: (k3_xboole_0(B_878, k4_xboole_0(A_879, B_878))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44083, c_47186])).
% 17.79/9.23  tff(c_47367, plain, (k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24314, c_47217])).
% 17.79/9.23  tff(c_48262, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47367, c_46])).
% 17.79/9.23  tff(c_48295, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_419, c_7548, c_48262])).
% 17.79/9.23  tff(c_294, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_50, c_283])).
% 17.79/9.23  tff(c_7625, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7548, c_294])).
% 17.79/9.23  tff(c_7650, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_7625])).
% 17.79/9.23  tff(c_8046, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_7650])).
% 17.79/9.23  tff(c_48341, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48295, c_8046])).
% 17.79/9.23  tff(c_48372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_48341])).
% 17.79/9.23  tff(c_48373, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_7650])).
% 17.79/9.23  tff(c_86, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 17.79/9.23  tff(c_1688, plain, (![A_168, B_169]: (v3_pre_topc(k1_tops_1(A_168, B_169), A_168) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.79/9.23  tff(c_1702, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_82, c_1688])).
% 17.79/9.23  tff(c_1709, plain, (v3_pre_topc(k1_tops_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_1702])).
% 17.79/9.23  tff(c_48383, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48373, c_1709])).
% 17.79/9.23  tff(c_48391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_48383])).
% 17.79/9.23  tff(c_48392, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_88])).
% 17.79/9.23  tff(c_48530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_48392])).
% 17.79/9.23  tff(c_48531, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_94])).
% 17.79/9.23  tff(c_48653, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48531, c_88])).
% 17.79/9.23  tff(c_49904, plain, (![A_991, B_992, C_993]: (k7_subset_1(A_991, B_992, C_993)=k4_xboole_0(B_992, C_993) | ~m1_subset_1(B_992, k1_zfmisc_1(A_991)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.79/9.23  tff(c_49920, plain, (![C_993]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_993)=k4_xboole_0('#skF_6', C_993))), inference(resolution, [status(thm)], [c_82, c_49904])).
% 17.79/9.23  tff(c_54624, plain, (![A_1136, B_1137]: (k7_subset_1(u1_struct_0(A_1136), B_1137, k2_tops_1(A_1136, B_1137))=k1_tops_1(A_1136, B_1137) | ~m1_subset_1(B_1137, k1_zfmisc_1(u1_struct_0(A_1136))) | ~l1_pre_topc(A_1136))), inference(cnfTransformation, [status(thm)], [f_135])).
% 17.79/9.23  tff(c_54640, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_82, c_54624])).
% 17.79/9.23  tff(c_54650, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_49920, c_54640])).
% 17.79/9.23  tff(c_48661, plain, (![B_914, A_915]: (B_914=A_915 | ~r1_tarski(B_914, A_915) | ~r1_tarski(A_915, B_914))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.79/9.23  tff(c_48672, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_50, c_48661])).
% 17.79/9.23  tff(c_54727, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_54650, c_48672])).
% 17.79/9.23  tff(c_54757, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54650, c_54727])).
% 17.79/9.23  tff(c_55192, plain, (~r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_54757])).
% 17.79/9.23  tff(c_57486, plain, (![B_1195, A_1196, C_1197]: (r1_tarski(B_1195, k1_tops_1(A_1196, C_1197)) | ~r1_tarski(B_1195, C_1197) | ~v3_pre_topc(B_1195, A_1196) | ~m1_subset_1(C_1197, k1_zfmisc_1(u1_struct_0(A_1196))) | ~m1_subset_1(B_1195, k1_zfmisc_1(u1_struct_0(A_1196))) | ~l1_pre_topc(A_1196))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.79/9.23  tff(c_57502, plain, (![B_1195]: (r1_tarski(B_1195, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_1195, '#skF_6') | ~v3_pre_topc(B_1195, '#skF_5') | ~m1_subset_1(B_1195, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_82, c_57486])).
% 17.79/9.23  tff(c_57612, plain, (![B_1201]: (r1_tarski(B_1201, k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski(B_1201, '#skF_6') | ~v3_pre_topc(B_1201, '#skF_5') | ~m1_subset_1(B_1201, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_57502])).
% 17.79/9.23  tff(c_57635, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_57612])).
% 17.79/9.23  tff(c_57647, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48531, c_44, c_57635])).
% 17.79/9.23  tff(c_57649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55192, c_57647])).
% 17.79/9.23  tff(c_57650, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_54757])).
% 17.79/9.23  tff(c_74, plain, (![A_43, B_45]: (k7_subset_1(u1_struct_0(A_43), k2_pre_topc(A_43, B_45), k1_tops_1(A_43, B_45))=k2_tops_1(A_43, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.79/9.23  tff(c_57671, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_57650, c_74])).
% 17.79/9.23  tff(c_57678, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_57671])).
% 17.79/9.23  tff(c_57680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48653, c_57678])).
% 17.79/9.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.79/9.23  
% 17.79/9.23  Inference rules
% 17.79/9.23  ----------------------
% 17.79/9.23  #Ref     : 0
% 17.79/9.23  #Sup     : 13796
% 17.79/9.23  #Fact    : 0
% 17.79/9.23  #Define  : 0
% 17.79/9.23  #Split   : 33
% 17.79/9.23  #Chain   : 0
% 17.79/9.23  #Close   : 0
% 17.79/9.23  
% 17.79/9.23  Ordering : KBO
% 17.79/9.23  
% 17.79/9.23  Simplification rules
% 17.79/9.23  ----------------------
% 17.79/9.23  #Subsume      : 3517
% 17.79/9.23  #Demod        : 12242
% 17.79/9.23  #Tautology    : 4451
% 17.79/9.23  #SimpNegUnit  : 311
% 17.79/9.23  #BackRed      : 315
% 17.79/9.23  
% 17.79/9.23  #Partial instantiations: 0
% 17.79/9.23  #Strategies tried      : 1
% 17.79/9.23  
% 17.79/9.23  Timing (in seconds)
% 17.79/9.23  ----------------------
% 17.79/9.23  Preprocessing        : 0.37
% 17.79/9.23  Parsing              : 0.19
% 17.79/9.23  CNF conversion       : 0.03
% 17.79/9.23  Main loop            : 8.04
% 17.79/9.23  Inferencing          : 1.47
% 17.79/9.23  Reduction            : 3.74
% 17.79/9.23  Demodulation         : 3.03
% 17.79/9.23  BG Simplification    : 0.17
% 17.79/9.23  Subsumption          : 2.20
% 17.79/9.23  Abstraction          : 0.26
% 17.79/9.23  MUC search           : 0.00
% 17.79/9.23  Cooper               : 0.00
% 17.79/9.23  Total                : 8.48
% 17.79/9.23  Index Insertion      : 0.00
% 17.79/9.23  Index Deletion       : 0.00
% 17.79/9.23  Index Matching       : 0.00
% 17.79/9.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
