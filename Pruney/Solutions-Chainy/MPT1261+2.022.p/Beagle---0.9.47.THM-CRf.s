%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 10.83s
% Output     : CNFRefutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 278 expanded)
%              Number of leaves         :   51 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 ( 531 expanded)
%              Number of equality atoms :   91 ( 168 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_48,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_54,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8057,plain,(
    ! [A_356,B_357,C_358] :
      ( k7_subset_1(A_356,B_357,C_358) = k4_xboole_0(B_357,C_358)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(A_356)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8063,plain,(
    ! [C_358] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_358) = k4_xboole_0('#skF_3',C_358) ),
    inference(resolution,[status(thm)],[c_56,c_8057])).

tff(c_62,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_118,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1698,plain,(
    ! [A_139,B_140,C_141] :
      ( k7_subset_1(A_139,B_140,C_141) = k4_xboole_0(B_140,C_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1705,plain,(
    ! [C_142] : k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',C_142) = k4_xboole_0('#skF_3',C_142) ),
    inference(resolution,[status(thm)],[c_56,c_1698])).

tff(c_68,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_256,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_68])).

tff(c_1711,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1705,c_256])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_572,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_601,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_572])).

tff(c_608,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_601])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(A_69,B_70)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_598,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_572])).

tff(c_607,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_598])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_187,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_754,plain,(
    ! [A_108,B_109] : k3_xboole_0(k4_xboole_0(A_108,B_109),A_108) = k4_xboole_0(A_108,B_109) ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_760,plain,(
    ! [A_108,B_109] : k5_xboole_0(k4_xboole_0(A_108,B_109),k4_xboole_0(A_108,B_109)) = k4_xboole_0(k4_xboole_0(A_108,B_109),A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_754,c_10])).

tff(c_811,plain,(
    ! [A_110,B_111] : k4_xboole_0(k4_xboole_0(A_110,B_111),A_110) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_760])).

tff(c_24,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_822,plain,(
    ! [A_110,B_111] : k2_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = k5_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_24])).

tff(c_857,plain,(
    ! [A_110,B_111] : k2_xboole_0(A_110,k4_xboole_0(A_110,B_111)) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_822])).

tff(c_1729,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_857])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2868,plain,(
    ! [A_166,B_167] :
      ( k4_subset_1(u1_struct_0(A_166),B_167,k2_tops_1(A_166,B_167)) = k2_pre_topc(A_166,B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2875,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_2868])).

tff(c_2880,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2875])).

tff(c_44,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k2_tops_1(A_43,B_44),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2078,plain,(
    ! [A_149,B_150,C_151] :
      ( k4_subset_1(A_149,B_150,C_151) = k2_xboole_0(B_150,C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6395,plain,(
    ! [A_281,B_282,B_283] :
      ( k4_subset_1(u1_struct_0(A_281),B_282,k2_tops_1(A_281,B_283)) = k2_xboole_0(B_282,k2_tops_1(A_281,B_283))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_44,c_2078])).

tff(c_6404,plain,(
    ! [B_283] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_283)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_283))
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_6395])).

tff(c_6473,plain,(
    ! [B_284] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_284)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_284))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6404])).

tff(c_6487,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_6473])).

tff(c_6495,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_2880,c_6487])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1982,plain,(
    ! [A_145,B_146] :
      ( v4_pre_topc(k2_pre_topc(A_145,B_146),A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1989,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1982])).

tff(c_1994,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1989])).

tff(c_6497,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6495,c_1994])).

tff(c_6499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_6497])).

tff(c_6500,plain,(
    k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_8064,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) != k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8063,c_6500])).

tff(c_26,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6549,plain,(
    ! [A_290,B_291] : k3_tarski(k2_tarski(A_290,B_291)) = k2_xboole_0(A_290,B_291) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6640,plain,(
    ! [A_298,B_299] : k3_tarski(k2_tarski(A_298,B_299)) = k2_xboole_0(B_299,A_298) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6549])).

tff(c_28,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6663,plain,(
    ! [B_300,A_301] : k2_xboole_0(B_300,A_301) = k2_xboole_0(A_301,B_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_6640,c_28])).

tff(c_6716,plain,(
    ! [A_302] : k2_xboole_0(k1_xboole_0,A_302) = A_302 ),
    inference(superposition,[status(thm),theory(equality)],[c_6663,c_12])).

tff(c_22,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k2_xboole_0(A_17,B_18)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6797,plain,(
    ! [A_306] : k4_xboole_0(k1_xboole_0,A_306) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6716,c_22])).

tff(c_6802,plain,(
    ! [A_306] : k5_xboole_0(A_306,k1_xboole_0) = k2_xboole_0(A_306,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6797,c_24])).

tff(c_6829,plain,(
    ! [A_306] : k5_xboole_0(A_306,k1_xboole_0) = A_306 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6802])).

tff(c_6535,plain,(
    ! [A_287,B_288] : k4_xboole_0(A_287,k2_xboole_0(A_287,B_288)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6545,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6535])).

tff(c_7036,plain,(
    ! [A_317,B_318] : k5_xboole_0(A_317,k3_xboole_0(A_317,B_318)) = k4_xboole_0(A_317,B_318) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7062,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7036])).

tff(c_7071,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6545,c_7062])).

tff(c_6501,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_8927,plain,(
    ! [A_379,B_380] :
      ( r1_tarski(k2_tops_1(A_379,B_380),B_380)
      | ~ v4_pre_topc(B_380,A_379)
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0(A_379)))
      | ~ l1_pre_topc(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8934,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_8927])).

tff(c_8939,plain,(
    r1_tarski(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6501,c_8934])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8943,plain,(
    k3_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k2_tops_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_8939,c_14])).

tff(c_8950,plain,(
    k5_xboole_0(k2_tops_1('#skF_2','#skF_3'),k2_tops_1('#skF_2','#skF_3')) = k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8943,c_10])).

tff(c_8965,plain,(
    k4_xboole_0(k2_tops_1('#skF_2','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7071,c_8950])).

tff(c_8988,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = k5_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8965,c_24])).

tff(c_9000,plain,(
    k2_xboole_0('#skF_3',k2_tops_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6829,c_8988])).

tff(c_9153,plain,(
    ! [A_381,B_382] :
      ( k2_tops_1(A_381,k3_subset_1(u1_struct_0(A_381),B_382)) = k2_tops_1(A_381,B_382)
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ l1_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_9160,plain,
    ( k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_9153])).

tff(c_9165,plain,(
    k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9160])).

tff(c_9209,plain,(
    ! [A_388,B_389] :
      ( k4_subset_1(u1_struct_0(A_388),B_389,k2_tops_1(A_388,B_389)) = k2_pre_topc(A_388,B_389)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9216,plain,
    ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_9209])).

tff(c_9221,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2','#skF_3')) = k2_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9216])).

tff(c_32,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k3_subset_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7278,plain,(
    ! [C_331,A_332,B_333] :
      ( r2_hidden(C_331,A_332)
      | ~ r2_hidden(C_331,B_333)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(A_332)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9184,plain,(
    ! [A_383,B_384,A_385] :
      ( r2_hidden('#skF_1'(A_383,B_384),A_385)
      | ~ m1_subset_1(A_383,k1_zfmisc_1(A_385))
      | r1_tarski(A_383,B_384) ) ),
    inference(resolution,[status(thm)],[c_6,c_7278])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9196,plain,(
    ! [A_386,A_387] :
      ( ~ m1_subset_1(A_386,k1_zfmisc_1(A_387))
      | r1_tarski(A_386,A_387) ) ),
    inference(resolution,[status(thm)],[c_9184,c_4])).

tff(c_9379,plain,(
    ! [A_396,B_397] :
      ( r1_tarski(k2_tops_1(A_396,B_397),u1_struct_0(A_396))
      | ~ m1_subset_1(B_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ l1_pre_topc(A_396) ) ),
    inference(resolution,[status(thm)],[c_44,c_9196])).

tff(c_9385,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9165,c_9379])).

tff(c_9389,plain,
    ( r1_tarski(k2_tops_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9385])).

tff(c_12491,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9389])).

tff(c_12494,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_32,c_12491])).

tff(c_12498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12494])).

tff(c_12500,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_9389])).

tff(c_8866,plain,(
    ! [A_372,B_373,C_374] :
      ( k4_subset_1(A_372,B_373,C_374) = k2_xboole_0(B_373,C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(A_372))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(A_372)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12958,plain,(
    ! [A_502,B_503,B_504] :
      ( k4_subset_1(u1_struct_0(A_502),B_503,k2_tops_1(A_502,B_504)) = k2_xboole_0(B_503,k2_tops_1(A_502,B_504))
      | ~ m1_subset_1(B_503,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_subset_1(B_504,k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ l1_pre_topc(A_502) ) ),
    inference(resolution,[status(thm)],[c_44,c_8866])).

tff(c_12967,plain,(
    ! [B_504] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_504)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_504))
      | ~ m1_subset_1(B_504,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_12958])).

tff(c_13355,plain,(
    ! [B_508] :
      ( k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',B_508)) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',B_508))
      | ~ m1_subset_1(B_508,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12967])).

tff(c_13358,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) = k2_xboole_0('#skF_3',k2_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12500,c_13355])).

tff(c_13371,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9000,c_9165,c_9221,c_9165,c_13358])).

tff(c_48,plain,(
    ! [A_47,B_49] :
      ( k7_subset_1(u1_struct_0(A_47),k2_pre_topc(A_47,B_49),k1_tops_1(A_47,B_49)) = k2_tops_1(A_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13384,plain,
    ( k7_subset_1(u1_struct_0('#skF_2'),'#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13371,c_48])).

tff(c_13388,plain,(
    k4_xboole_0('#skF_3',k1_tops_1('#skF_2','#skF_3')) = k2_tops_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_8063,c_13384])).

tff(c_13390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8064,c_13388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.83/4.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.08  
% 10.93/4.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.09  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.93/4.09  
% 10.93/4.09  %Foreground sorts:
% 10.93/4.09  
% 10.93/4.09  
% 10.93/4.09  %Background operators:
% 10.93/4.09  
% 10.93/4.09  
% 10.93/4.09  %Foreground operators:
% 10.93/4.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.93/4.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.93/4.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.93/4.09  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.93/4.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.93/4.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.93/4.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.93/4.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.93/4.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.93/4.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.93/4.09  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.93/4.09  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.93/4.09  tff('#skF_2', type, '#skF_2': $i).
% 10.93/4.09  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.93/4.09  tff('#skF_3', type, '#skF_3': $i).
% 10.93/4.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.93/4.09  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.93/4.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.93/4.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.93/4.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.93/4.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.93/4.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.93/4.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.93/4.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.93/4.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.93/4.09  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.93/4.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.93/4.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.93/4.09  
% 10.93/4.11  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 10.93/4.11  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.93/4.11  tff(f_48, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.93/4.11  tff(f_44, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.93/4.11  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.93/4.11  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.93/4.11  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 10.93/4.11  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 10.93/4.11  tff(f_46, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.93/4.11  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.93/4.11  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.93/4.11  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 10.93/4.11  tff(f_93, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 10.93/4.11  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.93/4.11  tff(f_101, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 10.93/4.11  tff(f_54, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.93/4.11  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.93/4.11  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 10.93/4.11  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 10.93/4.11  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.93/4.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.93/4.11  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 10.93/4.11  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 10.93/4.11  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.11  tff(c_8057, plain, (![A_356, B_357, C_358]: (k7_subset_1(A_356, B_357, C_358)=k4_xboole_0(B_357, C_358) | ~m1_subset_1(B_357, k1_zfmisc_1(A_356)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.93/4.11  tff(c_8063, plain, (![C_358]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_358)=k4_xboole_0('#skF_3', C_358))), inference(resolution, [status(thm)], [c_56, c_8057])).
% 10.93/4.11  tff(c_62, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.11  tff(c_118, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 10.93/4.11  tff(c_1698, plain, (![A_139, B_140, C_141]: (k7_subset_1(A_139, B_140, C_141)=k4_xboole_0(B_140, C_141) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.93/4.11  tff(c_1705, plain, (![C_142]: (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', C_142)=k4_xboole_0('#skF_3', C_142))), inference(resolution, [status(thm)], [c_56, c_1698])).
% 10.93/4.11  tff(c_68, plain, (v4_pre_topc('#skF_3', '#skF_2') | k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.11  tff(c_256, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_118, c_68])).
% 10.93/4.11  tff(c_1711, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1705, c_256])).
% 10.93/4.11  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.93/4.11  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.93/4.11  tff(c_572, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.11  tff(c_601, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_572])).
% 10.93/4.11  tff(c_608, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_601])).
% 10.93/4.11  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.93/4.11  tff(c_152, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(A_69, B_70))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.11  tff(c_162, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_152])).
% 10.93/4.11  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.93/4.11  tff(c_598, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_572])).
% 10.93/4.11  tff(c_607, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_598])).
% 10.93/4.11  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.93/4.11  tff(c_187, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.93/4.11  tff(c_754, plain, (![A_108, B_109]: (k3_xboole_0(k4_xboole_0(A_108, B_109), A_108)=k4_xboole_0(A_108, B_109))), inference(resolution, [status(thm)], [c_18, c_187])).
% 10.93/4.11  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.11  tff(c_760, plain, (![A_108, B_109]: (k5_xboole_0(k4_xboole_0(A_108, B_109), k4_xboole_0(A_108, B_109))=k4_xboole_0(k4_xboole_0(A_108, B_109), A_108))), inference(superposition, [status(thm), theory('equality')], [c_754, c_10])).
% 10.93/4.11  tff(c_811, plain, (![A_110, B_111]: (k4_xboole_0(k4_xboole_0(A_110, B_111), A_110)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_607, c_760])).
% 10.93/4.11  tff(c_24, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.93/4.11  tff(c_822, plain, (![A_110, B_111]: (k2_xboole_0(A_110, k4_xboole_0(A_110, B_111))=k5_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_811, c_24])).
% 10.93/4.11  tff(c_857, plain, (![A_110, B_111]: (k2_xboole_0(A_110, k4_xboole_0(A_110, B_111))=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_608, c_822])).
% 10.93/4.11  tff(c_1729, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1711, c_857])).
% 10.93/4.11  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.11  tff(c_2868, plain, (![A_166, B_167]: (k4_subset_1(u1_struct_0(A_166), B_167, k2_tops_1(A_166, B_167))=k2_pre_topc(A_166, B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.93/4.11  tff(c_2875, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_2868])).
% 10.93/4.11  tff(c_2880, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2875])).
% 10.93/4.11  tff(c_44, plain, (![A_43, B_44]: (m1_subset_1(k2_tops_1(A_43, B_44), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.93/4.11  tff(c_2078, plain, (![A_149, B_150, C_151]: (k4_subset_1(A_149, B_150, C_151)=k2_xboole_0(B_150, C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(A_149)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_149)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.93/4.11  tff(c_6395, plain, (![A_281, B_282, B_283]: (k4_subset_1(u1_struct_0(A_281), B_282, k2_tops_1(A_281, B_283))=k2_xboole_0(B_282, k2_tops_1(A_281, B_283)) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_44, c_2078])).
% 10.93/4.11  tff(c_6404, plain, (![B_283]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_283))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_283)) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_6395])).
% 10.93/4.11  tff(c_6473, plain, (![B_284]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_284))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_284)) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6404])).
% 10.93/4.11  tff(c_6487, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_6473])).
% 10.93/4.11  tff(c_6495, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_2880, c_6487])).
% 10.93/4.11  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.93/4.11  tff(c_1982, plain, (![A_145, B_146]: (v4_pre_topc(k2_pre_topc(A_145, B_146), A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.93/4.11  tff(c_1989, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1982])).
% 10.93/4.11  tff(c_1994, plain, (v4_pre_topc(k2_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1989])).
% 10.93/4.11  tff(c_6497, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6495, c_1994])).
% 10.93/4.11  tff(c_6499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_6497])).
% 10.93/4.11  tff(c_6500, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 10.93/4.11  tff(c_8064, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))!=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8063, c_6500])).
% 10.93/4.11  tff(c_26, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.93/4.11  tff(c_6549, plain, (![A_290, B_291]: (k3_tarski(k2_tarski(A_290, B_291))=k2_xboole_0(A_290, B_291))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.93/4.11  tff(c_6640, plain, (![A_298, B_299]: (k3_tarski(k2_tarski(A_298, B_299))=k2_xboole_0(B_299, A_298))), inference(superposition, [status(thm), theory('equality')], [c_26, c_6549])).
% 10.93/4.11  tff(c_28, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.93/4.11  tff(c_6663, plain, (![B_300, A_301]: (k2_xboole_0(B_300, A_301)=k2_xboole_0(A_301, B_300))), inference(superposition, [status(thm), theory('equality')], [c_6640, c_28])).
% 10.93/4.11  tff(c_6716, plain, (![A_302]: (k2_xboole_0(k1_xboole_0, A_302)=A_302)), inference(superposition, [status(thm), theory('equality')], [c_6663, c_12])).
% 10.93/4.11  tff(c_22, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k2_xboole_0(A_17, B_18))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.11  tff(c_6797, plain, (![A_306]: (k4_xboole_0(k1_xboole_0, A_306)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6716, c_22])).
% 10.93/4.11  tff(c_6802, plain, (![A_306]: (k5_xboole_0(A_306, k1_xboole_0)=k2_xboole_0(A_306, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6797, c_24])).
% 10.93/4.11  tff(c_6829, plain, (![A_306]: (k5_xboole_0(A_306, k1_xboole_0)=A_306)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6802])).
% 10.93/4.11  tff(c_6535, plain, (![A_287, B_288]: (k4_xboole_0(A_287, k2_xboole_0(A_287, B_288))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.93/4.11  tff(c_6545, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_6535])).
% 10.93/4.11  tff(c_7036, plain, (![A_317, B_318]: (k5_xboole_0(A_317, k3_xboole_0(A_317, B_318))=k4_xboole_0(A_317, B_318))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.93/4.11  tff(c_7062, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7036])).
% 10.93/4.11  tff(c_7071, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6545, c_7062])).
% 10.93/4.11  tff(c_6501, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 10.93/4.11  tff(c_8927, plain, (![A_379, B_380]: (r1_tarski(k2_tops_1(A_379, B_380), B_380) | ~v4_pre_topc(B_380, A_379) | ~m1_subset_1(B_380, k1_zfmisc_1(u1_struct_0(A_379))) | ~l1_pre_topc(A_379))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.93/4.11  tff(c_8934, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_8927])).
% 10.93/4.11  tff(c_8939, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6501, c_8934])).
% 10.93/4.11  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.93/4.11  tff(c_8943, plain, (k3_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k2_tops_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_8939, c_14])).
% 10.93/4.11  tff(c_8950, plain, (k5_xboole_0(k2_tops_1('#skF_2', '#skF_3'), k2_tops_1('#skF_2', '#skF_3'))=k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8943, c_10])).
% 10.93/4.11  tff(c_8965, plain, (k4_xboole_0(k2_tops_1('#skF_2', '#skF_3'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7071, c_8950])).
% 10.93/4.11  tff(c_8988, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8965, c_24])).
% 10.93/4.11  tff(c_9000, plain, (k2_xboole_0('#skF_3', k2_tops_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6829, c_8988])).
% 10.93/4.11  tff(c_9153, plain, (![A_381, B_382]: (k2_tops_1(A_381, k3_subset_1(u1_struct_0(A_381), B_382))=k2_tops_1(A_381, B_382) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_381))) | ~l1_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.93/4.11  tff(c_9160, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_9153])).
% 10.93/4.11  tff(c_9165, plain, (k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9160])).
% 10.93/4.11  tff(c_9209, plain, (![A_388, B_389]: (k4_subset_1(u1_struct_0(A_388), B_389, k2_tops_1(A_388, B_389))=k2_pre_topc(A_388, B_389) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.93/4.11  tff(c_9216, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_9209])).
% 10.93/4.11  tff(c_9221, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9216])).
% 10.93/4.11  tff(c_32, plain, (![A_27, B_28]: (m1_subset_1(k3_subset_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.93/4.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.93/4.11  tff(c_7278, plain, (![C_331, A_332, B_333]: (r2_hidden(C_331, A_332) | ~r2_hidden(C_331, B_333) | ~m1_subset_1(B_333, k1_zfmisc_1(A_332)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.93/4.11  tff(c_9184, plain, (![A_383, B_384, A_385]: (r2_hidden('#skF_1'(A_383, B_384), A_385) | ~m1_subset_1(A_383, k1_zfmisc_1(A_385)) | r1_tarski(A_383, B_384))), inference(resolution, [status(thm)], [c_6, c_7278])).
% 10.93/4.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.93/4.11  tff(c_9196, plain, (![A_386, A_387]: (~m1_subset_1(A_386, k1_zfmisc_1(A_387)) | r1_tarski(A_386, A_387))), inference(resolution, [status(thm)], [c_9184, c_4])).
% 10.93/4.11  tff(c_9379, plain, (![A_396, B_397]: (r1_tarski(k2_tops_1(A_396, B_397), u1_struct_0(A_396)) | ~m1_subset_1(B_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~l1_pre_topc(A_396))), inference(resolution, [status(thm)], [c_44, c_9196])).
% 10.93/4.11  tff(c_9385, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9165, c_9379])).
% 10.93/4.11  tff(c_9389, plain, (r1_tarski(k2_tops_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9385])).
% 10.93/4.11  tff(c_12491, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_9389])).
% 10.93/4.11  tff(c_12494, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_32, c_12491])).
% 10.93/4.11  tff(c_12498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_12494])).
% 10.93/4.11  tff(c_12500, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_9389])).
% 10.93/4.11  tff(c_8866, plain, (![A_372, B_373, C_374]: (k4_subset_1(A_372, B_373, C_374)=k2_xboole_0(B_373, C_374) | ~m1_subset_1(C_374, k1_zfmisc_1(A_372)) | ~m1_subset_1(B_373, k1_zfmisc_1(A_372)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.93/4.11  tff(c_12958, plain, (![A_502, B_503, B_504]: (k4_subset_1(u1_struct_0(A_502), B_503, k2_tops_1(A_502, B_504))=k2_xboole_0(B_503, k2_tops_1(A_502, B_504)) | ~m1_subset_1(B_503, k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_subset_1(B_504, k1_zfmisc_1(u1_struct_0(A_502))) | ~l1_pre_topc(A_502))), inference(resolution, [status(thm)], [c_44, c_8866])).
% 10.93/4.11  tff(c_12967, plain, (![B_504]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_504))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_504)) | ~m1_subset_1(B_504, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_12958])).
% 10.93/4.11  tff(c_13355, plain, (![B_508]: (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', B_508))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', B_508)) | ~m1_subset_1(B_508, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12967])).
% 10.93/4.11  tff(c_13358, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))=k2_xboole_0('#skF_3', k2_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')))), inference(resolution, [status(thm)], [c_12500, c_13355])).
% 10.93/4.11  tff(c_13371, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9000, c_9165, c_9221, c_9165, c_13358])).
% 10.93/4.11  tff(c_48, plain, (![A_47, B_49]: (k7_subset_1(u1_struct_0(A_47), k2_pre_topc(A_47, B_49), k1_tops_1(A_47, B_49))=k2_tops_1(A_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.93/4.11  tff(c_13384, plain, (k7_subset_1(u1_struct_0('#skF_2'), '#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13371, c_48])).
% 10.93/4.11  tff(c_13388, plain, (k4_xboole_0('#skF_3', k1_tops_1('#skF_2', '#skF_3'))=k2_tops_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_8063, c_13384])).
% 10.93/4.11  tff(c_13390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8064, c_13388])).
% 10.93/4.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.93/4.11  
% 10.93/4.11  Inference rules
% 10.93/4.11  ----------------------
% 10.93/4.11  #Ref     : 0
% 10.93/4.11  #Sup     : 3238
% 10.93/4.11  #Fact    : 0
% 10.93/4.11  #Define  : 0
% 10.93/4.11  #Split   : 5
% 10.93/4.11  #Chain   : 0
% 10.93/4.11  #Close   : 0
% 10.93/4.11  
% 10.93/4.11  Ordering : KBO
% 10.93/4.11  
% 10.93/4.11  Simplification rules
% 10.93/4.11  ----------------------
% 10.93/4.11  #Subsume      : 263
% 10.93/4.11  #Demod        : 3640
% 10.93/4.11  #Tautology    : 2421
% 10.93/4.11  #SimpNegUnit  : 3
% 10.93/4.11  #BackRed      : 10
% 10.93/4.11  
% 10.93/4.11  #Partial instantiations: 0
% 10.93/4.11  #Strategies tried      : 1
% 10.93/4.11  
% 10.93/4.11  Timing (in seconds)
% 10.93/4.11  ----------------------
% 10.93/4.11  Preprocessing        : 0.58
% 10.93/4.11  Parsing              : 0.32
% 10.93/4.11  CNF conversion       : 0.04
% 10.93/4.11  Main loop            : 2.63
% 10.93/4.11  Inferencing          : 0.78
% 10.93/4.11  Reduction            : 1.20
% 10.93/4.11  Demodulation         : 0.98
% 10.93/4.11  BG Simplification    : 0.08
% 10.93/4.11  Subsumption          : 0.41
% 10.93/4.11  Abstraction          : 0.11
% 10.93/4.11  MUC search           : 0.00
% 10.93/4.11  Cooper               : 0.00
% 10.93/4.11  Total                : 3.26
% 10.93/4.11  Index Insertion      : 0.00
% 10.93/4.11  Index Deletion       : 0.00
% 10.93/4.11  Index Matching       : 0.00
% 10.93/4.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
