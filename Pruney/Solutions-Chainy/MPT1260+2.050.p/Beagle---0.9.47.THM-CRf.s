%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:06 EST 2020

% Result     : Theorem 21.31s
% Output     : CNFRefutation 21.31s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 239 expanded)
%              Number of leaves         :   38 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 568 expanded)
%              Number of equality atoms :   65 ( 170 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_100,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_72,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_147,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_70,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_60,plain,(
    ! [C_45,A_33,D_47,B_41] :
      ( v3_pre_topc(C_45,A_33)
      | k1_tops_1(A_33,C_45) != C_45
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(B_41)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5829,plain,(
    ! [D_251,B_252] :
      ( ~ m1_subset_1(D_251,k1_zfmisc_1(u1_struct_0(B_252)))
      | ~ l1_pre_topc(B_252) ) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_5832,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_5829])).

tff(c_5836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5832])).

tff(c_6899,plain,(
    ! [C_263,A_264] :
      ( v3_pre_topc(C_263,A_264)
      | k1_tops_1(A_264,C_263) != C_263
      | ~ m1_subset_1(C_263,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264) ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6905,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6899])).

tff(c_6909,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_6905])).

tff(c_6910,plain,(
    k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_6909])).

tff(c_44,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,(
    ! [B_16] : k3_xboole_0(B_16,B_16) = B_16 ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_38,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_916,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r2_hidden('#skF_3'(A_122,B_123,C_124),B_123)
      | r2_hidden('#skF_4'(A_122,B_123,C_124),C_124)
      | k4_xboole_0(A_122,B_123) = C_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_929,plain,(
    ! [A_125,C_126] :
      ( r2_hidden('#skF_4'(A_125,A_125,C_126),C_126)
      | k4_xboole_0(A_125,A_125) = C_126 ) ),
    inference(resolution,[status(thm)],[c_38,c_916])).

tff(c_26,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,A_9)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_961,plain,(
    ! [A_125,A_9,B_10] :
      ( r2_hidden('#skF_4'(A_125,A_125,k4_xboole_0(A_9,B_10)),A_9)
      | k4_xboole_0(A_9,B_10) = k4_xboole_0(A_125,A_125) ) ),
    inference(resolution,[status(thm)],[c_929,c_26])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2664,plain,(
    ! [A_190,A_191,B_192] :
      ( ~ r2_hidden('#skF_4'(A_190,A_190,k4_xboole_0(A_191,B_192)),B_192)
      | k4_xboole_0(A_191,B_192) = k4_xboole_0(A_190,A_190) ) ),
    inference(resolution,[status(thm)],[c_929,c_24])).

tff(c_2801,plain,(
    ! [A_195,A_194] : k4_xboole_0(A_195,A_195) = k4_xboole_0(A_194,A_194) ),
    inference(resolution,[status(thm)],[c_961,c_2664])).

tff(c_50,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2948,plain,(
    ! [A_194,A_195] : k4_xboole_0(A_194,k4_xboole_0(A_195,A_195)) = k3_xboole_0(A_194,A_194) ),
    inference(superposition,[status(thm),theory(equality)],[c_2801,c_50])).

tff(c_2986,plain,(
    ! [A_194,A_195] : k4_xboole_0(A_194,k4_xboole_0(A_195,A_195)) = A_194 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2948])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_964,plain,(
    ! [A_125,A_3,B_4] :
      ( r2_hidden('#skF_4'(A_125,A_125,k3_xboole_0(A_3,B_4)),A_3)
      | k4_xboole_0(A_125,A_125) = k3_xboole_0(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_929,c_8])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_962,plain,(
    ! [A_125,A_3,B_4] :
      ( r2_hidden('#skF_4'(A_125,A_125,k3_xboole_0(A_3,B_4)),B_4)
      | k4_xboole_0(A_125,A_125) = k3_xboole_0(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_929,c_6])).

tff(c_477,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k2_pre_topc(A_102,B_103),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_23,B_24,C_25] :
      ( k7_subset_1(A_23,B_24,C_25) = k4_xboole_0(B_24,C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8543,plain,(
    ! [A_294,B_295,C_296] :
      ( k7_subset_1(u1_struct_0(A_294),k2_pre_topc(A_294,B_295),C_296) = k4_xboole_0(k2_pre_topc(A_294,B_295),C_296)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ l1_pre_topc(A_294) ) ),
    inference(resolution,[status(thm)],[c_477,c_52])).

tff(c_8547,plain,(
    ! [C_296] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_296) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_296)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_8543])).

tff(c_8695,plain,(
    ! [C_300] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_300) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_300) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_8547])).

tff(c_78,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_246,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_78])).

tff(c_8705,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8695,c_246])).

tff(c_8777,plain,(
    ! [D_301] :
      ( ~ r2_hidden(D_301,'#skF_6')
      | ~ r2_hidden(D_301,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8705,c_24])).

tff(c_58040,plain,(
    ! [A_648,A_649] :
      ( ~ r2_hidden('#skF_4'(A_648,A_648,k3_xboole_0(A_649,k2_tops_1('#skF_5','#skF_6'))),'#skF_6')
      | k4_xboole_0(A_648,A_648) = k3_xboole_0(A_649,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_962,c_8777])).

tff(c_58114,plain,(
    ! [A_650] : k4_xboole_0(A_650,A_650) = k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_964,c_58040])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2531,plain,(
    ! [A_187,A_188,B_189] :
      ( r2_hidden('#skF_4'(A_187,A_187,k4_xboole_0(A_188,B_189)),A_188)
      | k4_xboole_0(A_188,B_189) = k4_xboole_0(A_187,A_187) ) ),
    inference(resolution,[status(thm)],[c_929,c_26])).

tff(c_412,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_415,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_98) = k4_xboole_0('#skF_6',C_98) ),
    inference(resolution,[status(thm)],[c_66,c_412])).

tff(c_1694,plain,(
    ! [A_162,B_163] :
      ( k7_subset_1(u1_struct_0(A_162),B_163,k2_tops_1(A_162,B_163)) = k1_tops_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1698,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1694])).

tff(c_1702,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_415,c_1698])).

tff(c_1730,plain,(
    ! [D_14] :
      ( r2_hidden(D_14,'#skF_6')
      | ~ r2_hidden(D_14,k1_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_26])).

tff(c_38268,plain,(
    ! [A_531,B_532] :
      ( r2_hidden('#skF_4'(A_531,A_531,k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),B_532)),'#skF_6')
      | k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),B_532) = k4_xboole_0(A_531,A_531) ) ),
    inference(resolution,[status(thm)],[c_2531,c_1730])).

tff(c_963,plain,(
    ! [A_125,A_9,B_10] :
      ( ~ r2_hidden('#skF_4'(A_125,A_125,k4_xboole_0(A_9,B_10)),B_10)
      | k4_xboole_0(A_9,B_10) = k4_xboole_0(A_125,A_125) ) ),
    inference(resolution,[status(thm)],[c_929,c_24])).

tff(c_38393,plain,(
    ! [A_533] : k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),'#skF_6') = k4_xboole_0(A_533,A_533) ),
    inference(resolution,[status(thm)],[c_38268,c_963])).

tff(c_38747,plain,(
    ! [A_533] : k4_xboole_0(k1_tops_1('#skF_5','#skF_6'),k4_xboole_0(A_533,A_533)) = k3_xboole_0(k1_tops_1('#skF_5','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38393,c_50])).

tff(c_38860,plain,(
    k3_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2986,c_38747])).

tff(c_1733,plain,(
    k4_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) = k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_50])).

tff(c_1824,plain,(
    k4_xboole_0('#skF_6',k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6'))) = k3_xboole_0('#skF_6',k1_tops_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1733,c_50])).

tff(c_39474,plain,(
    k4_xboole_0('#skF_6',k3_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6'))) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38860,c_1824])).

tff(c_58241,plain,(
    ! [A_650] : k4_xboole_0('#skF_6',k4_xboole_0(A_650,A_650)) = k1_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_58114,c_39474])).

tff(c_58617,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2986,c_58241])).

tff(c_58619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6910,c_58617])).

tff(c_58620,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_58621,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_62,plain,(
    ! [B_41,D_47,C_45,A_33] :
      ( k1_tops_1(B_41,D_47) = D_47
      | ~ v3_pre_topc(D_47,B_41)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0(B_41)))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(B_41)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_65430,plain,(
    ! [C_856,A_857] :
      ( ~ m1_subset_1(C_856,k1_zfmisc_1(u1_struct_0(A_857)))
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857) ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_65436,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_65430])).

tff(c_65441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_65436])).

tff(c_66064,plain,(
    ! [B_866,D_867] :
      ( k1_tops_1(B_866,D_867) = D_867
      | ~ v3_pre_topc(D_867,B_866)
      | ~ m1_subset_1(D_867,k1_zfmisc_1(u1_struct_0(B_866)))
      | ~ l1_pre_topc(B_866) ) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66070,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_66064])).

tff(c_66074,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_58621,c_66070])).

tff(c_58,plain,(
    ! [A_30,B_32] :
      ( k7_subset_1(u1_struct_0(A_30),k2_pre_topc(A_30,B_32),k1_tops_1(A_30,B_32)) = k2_tops_1(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_66094,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_66074,c_58])).

tff(c_66098,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_66094])).

tff(c_66100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58620,c_66098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:47:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.31/12.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.31/12.07  
% 21.31/12.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.31/12.07  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 21.31/12.07  
% 21.31/12.07  %Foreground sorts:
% 21.31/12.07  
% 21.31/12.07  
% 21.31/12.07  %Background operators:
% 21.31/12.07  
% 21.31/12.07  
% 21.31/12.07  %Foreground operators:
% 21.31/12.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 21.31/12.07  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 21.31/12.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.31/12.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.31/12.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.31/12.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 21.31/12.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 21.31/12.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 21.31/12.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.31/12.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.31/12.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.31/12.07  tff('#skF_5', type, '#skF_5': $i).
% 21.31/12.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 21.31/12.07  tff('#skF_6', type, '#skF_6': $i).
% 21.31/12.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 21.31/12.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 21.31/12.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.31/12.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.31/12.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 21.31/12.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.31/12.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 21.31/12.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.31/12.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 21.31/12.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 21.31/12.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.31/12.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.31/12.07  
% 21.31/12.09  tff(f_119, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 21.31/12.09  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 21.31/12.09  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.31/12.09  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 21.31/12.09  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 21.31/12.09  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.31/12.09  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 21.31/12.09  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 21.31/12.09  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 21.31/12.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 21.31/12.09  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 21.31/12.09  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 21.31/12.09  tff(c_72, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.31/12.09  tff(c_147, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 21.31/12.09  tff(c_70, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.31/12.09  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.31/12.09  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.31/12.09  tff(c_60, plain, (![C_45, A_33, D_47, B_41]: (v3_pre_topc(C_45, A_33) | k1_tops_1(A_33, C_45)!=C_45 | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(B_41))) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(B_41) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 21.31/12.09  tff(c_5829, plain, (![D_251, B_252]: (~m1_subset_1(D_251, k1_zfmisc_1(u1_struct_0(B_252))) | ~l1_pre_topc(B_252))), inference(splitLeft, [status(thm)], [c_60])).
% 21.31/12.09  tff(c_5832, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_5829])).
% 21.31/12.09  tff(c_5836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5832])).
% 21.31/12.09  tff(c_6899, plain, (![C_263, A_264]: (v3_pre_topc(C_263, A_264) | k1_tops_1(A_264, C_263)!=C_263 | ~m1_subset_1(C_263, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264))), inference(splitRight, [status(thm)], [c_60])).
% 21.31/12.09  tff(c_6905, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_6899])).
% 21.31/12.09  tff(c_6909, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_6905])).
% 21.31/12.09  tff(c_6910, plain, (k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_147, c_6909])).
% 21.31/12.09  tff(c_44, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 21.31/12.09  tff(c_123, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 21.31/12.09  tff(c_127, plain, (![B_16]: (k3_xboole_0(B_16, B_16)=B_16)), inference(resolution, [status(thm)], [c_44, c_123])).
% 21.31/12.09  tff(c_38, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_3'(A_9, B_10, C_11), A_9) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.31/12.09  tff(c_916, plain, (![A_122, B_123, C_124]: (~r2_hidden('#skF_3'(A_122, B_123, C_124), B_123) | r2_hidden('#skF_4'(A_122, B_123, C_124), C_124) | k4_xboole_0(A_122, B_123)=C_124)), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.31/12.09  tff(c_929, plain, (![A_125, C_126]: (r2_hidden('#skF_4'(A_125, A_125, C_126), C_126) | k4_xboole_0(A_125, A_125)=C_126)), inference(resolution, [status(thm)], [c_38, c_916])).
% 21.31/12.09  tff(c_26, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, A_9) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.31/12.09  tff(c_961, plain, (![A_125, A_9, B_10]: (r2_hidden('#skF_4'(A_125, A_125, k4_xboole_0(A_9, B_10)), A_9) | k4_xboole_0(A_9, B_10)=k4_xboole_0(A_125, A_125))), inference(resolution, [status(thm)], [c_929, c_26])).
% 21.31/12.09  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 21.31/12.09  tff(c_2664, plain, (![A_190, A_191, B_192]: (~r2_hidden('#skF_4'(A_190, A_190, k4_xboole_0(A_191, B_192)), B_192) | k4_xboole_0(A_191, B_192)=k4_xboole_0(A_190, A_190))), inference(resolution, [status(thm)], [c_929, c_24])).
% 21.31/12.09  tff(c_2801, plain, (![A_195, A_194]: (k4_xboole_0(A_195, A_195)=k4_xboole_0(A_194, A_194))), inference(resolution, [status(thm)], [c_961, c_2664])).
% 21.31/12.09  tff(c_50, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 21.31/12.09  tff(c_2948, plain, (![A_194, A_195]: (k4_xboole_0(A_194, k4_xboole_0(A_195, A_195))=k3_xboole_0(A_194, A_194))), inference(superposition, [status(thm), theory('equality')], [c_2801, c_50])).
% 21.31/12.09  tff(c_2986, plain, (![A_194, A_195]: (k4_xboole_0(A_194, k4_xboole_0(A_195, A_195))=A_194)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2948])).
% 21.31/12.09  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.31/12.09  tff(c_964, plain, (![A_125, A_3, B_4]: (r2_hidden('#skF_4'(A_125, A_125, k3_xboole_0(A_3, B_4)), A_3) | k4_xboole_0(A_125, A_125)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_929, c_8])).
% 21.31/12.09  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.31/12.09  tff(c_962, plain, (![A_125, A_3, B_4]: (r2_hidden('#skF_4'(A_125, A_125, k3_xboole_0(A_3, B_4)), B_4) | k4_xboole_0(A_125, A_125)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_929, c_6])).
% 21.31/12.09  tff(c_477, plain, (![A_102, B_103]: (m1_subset_1(k2_pre_topc(A_102, B_103), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_72])).
% 21.31/12.09  tff(c_52, plain, (![A_23, B_24, C_25]: (k7_subset_1(A_23, B_24, C_25)=k4_xboole_0(B_24, C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.31/12.09  tff(c_8543, plain, (![A_294, B_295, C_296]: (k7_subset_1(u1_struct_0(A_294), k2_pre_topc(A_294, B_295), C_296)=k4_xboole_0(k2_pre_topc(A_294, B_295), C_296) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_294))) | ~l1_pre_topc(A_294))), inference(resolution, [status(thm)], [c_477, c_52])).
% 21.31/12.09  tff(c_8547, plain, (![C_296]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_296)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_296) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_8543])).
% 21.31/12.09  tff(c_8695, plain, (![C_300]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_300)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_300))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_8547])).
% 21.31/12.09  tff(c_78, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 21.31/12.09  tff(c_246, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_147, c_78])).
% 21.31/12.09  tff(c_8705, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8695, c_246])).
% 21.31/12.09  tff(c_8777, plain, (![D_301]: (~r2_hidden(D_301, '#skF_6') | ~r2_hidden(D_301, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8705, c_24])).
% 21.31/12.09  tff(c_58040, plain, (![A_648, A_649]: (~r2_hidden('#skF_4'(A_648, A_648, k3_xboole_0(A_649, k2_tops_1('#skF_5', '#skF_6'))), '#skF_6') | k4_xboole_0(A_648, A_648)=k3_xboole_0(A_649, k2_tops_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_962, c_8777])).
% 21.31/12.09  tff(c_58114, plain, (![A_650]: (k4_xboole_0(A_650, A_650)=k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_964, c_58040])).
% 21.31/12.09  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.31/12.09  tff(c_2531, plain, (![A_187, A_188, B_189]: (r2_hidden('#skF_4'(A_187, A_187, k4_xboole_0(A_188, B_189)), A_188) | k4_xboole_0(A_188, B_189)=k4_xboole_0(A_187, A_187))), inference(resolution, [status(thm)], [c_929, c_26])).
% 21.31/12.09  tff(c_412, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 21.31/12.09  tff(c_415, plain, (![C_98]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_98)=k4_xboole_0('#skF_6', C_98))), inference(resolution, [status(thm)], [c_66, c_412])).
% 21.31/12.09  tff(c_1694, plain, (![A_162, B_163]: (k7_subset_1(u1_struct_0(A_162), B_163, k2_tops_1(A_162, B_163))=k1_tops_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_107])).
% 21.31/12.09  tff(c_1698, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1694])).
% 21.31/12.09  tff(c_1702, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_415, c_1698])).
% 21.31/12.09  tff(c_1730, plain, (![D_14]: (r2_hidden(D_14, '#skF_6') | ~r2_hidden(D_14, k1_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_26])).
% 21.31/12.09  tff(c_38268, plain, (![A_531, B_532]: (r2_hidden('#skF_4'(A_531, A_531, k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), B_532)), '#skF_6') | k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), B_532)=k4_xboole_0(A_531, A_531))), inference(resolution, [status(thm)], [c_2531, c_1730])).
% 21.31/12.09  tff(c_963, plain, (![A_125, A_9, B_10]: (~r2_hidden('#skF_4'(A_125, A_125, k4_xboole_0(A_9, B_10)), B_10) | k4_xboole_0(A_9, B_10)=k4_xboole_0(A_125, A_125))), inference(resolution, [status(thm)], [c_929, c_24])).
% 21.31/12.09  tff(c_38393, plain, (![A_533]: (k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), '#skF_6')=k4_xboole_0(A_533, A_533))), inference(resolution, [status(thm)], [c_38268, c_963])).
% 21.31/12.09  tff(c_38747, plain, (![A_533]: (k4_xboole_0(k1_tops_1('#skF_5', '#skF_6'), k4_xboole_0(A_533, A_533))=k3_xboole_0(k1_tops_1('#skF_5', '#skF_6'), '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_38393, c_50])).
% 21.31/12.09  tff(c_38860, plain, (k3_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2986, c_38747])).
% 21.31/12.09  tff(c_1733, plain, (k4_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))=k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1702, c_50])).
% 21.31/12.09  tff(c_1824, plain, (k4_xboole_0('#skF_6', k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6')))=k3_xboole_0('#skF_6', k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1733, c_50])).
% 21.31/12.09  tff(c_39474, plain, (k4_xboole_0('#skF_6', k3_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6')))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38860, c_1824])).
% 21.31/12.09  tff(c_58241, plain, (![A_650]: (k4_xboole_0('#skF_6', k4_xboole_0(A_650, A_650))=k1_tops_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_58114, c_39474])).
% 21.31/12.09  tff(c_58617, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2986, c_58241])).
% 21.31/12.09  tff(c_58619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6910, c_58617])).
% 21.31/12.09  tff(c_58620, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 21.31/12.09  tff(c_58621, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_72])).
% 21.31/12.09  tff(c_62, plain, (![B_41, D_47, C_45, A_33]: (k1_tops_1(B_41, D_47)=D_47 | ~v3_pre_topc(D_47, B_41) | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0(B_41))) | ~m1_subset_1(C_45, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(B_41) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 21.31/12.09  tff(c_65430, plain, (![C_856, A_857]: (~m1_subset_1(C_856, k1_zfmisc_1(u1_struct_0(A_857))) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857))), inference(splitLeft, [status(thm)], [c_62])).
% 21.31/12.09  tff(c_65436, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_65430])).
% 21.31/12.09  tff(c_65441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_65436])).
% 21.31/12.09  tff(c_66064, plain, (![B_866, D_867]: (k1_tops_1(B_866, D_867)=D_867 | ~v3_pre_topc(D_867, B_866) | ~m1_subset_1(D_867, k1_zfmisc_1(u1_struct_0(B_866))) | ~l1_pre_topc(B_866))), inference(splitRight, [status(thm)], [c_62])).
% 21.31/12.09  tff(c_66070, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_66064])).
% 21.31/12.09  tff(c_66074, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_58621, c_66070])).
% 21.31/12.09  tff(c_58, plain, (![A_30, B_32]: (k7_subset_1(u1_struct_0(A_30), k2_pre_topc(A_30, B_32), k1_tops_1(A_30, B_32))=k2_tops_1(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.31/12.09  tff(c_66094, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_66074, c_58])).
% 21.31/12.09  tff(c_66098, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_66094])).
% 21.31/12.09  tff(c_66100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58620, c_66098])).
% 21.31/12.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.31/12.09  
% 21.31/12.09  Inference rules
% 21.31/12.09  ----------------------
% 21.31/12.09  #Ref     : 0
% 21.31/12.09  #Sup     : 18354
% 21.31/12.09  #Fact    : 0
% 21.31/12.09  #Define  : 0
% 21.31/12.09  #Split   : 5
% 21.31/12.09  #Chain   : 0
% 21.31/12.09  #Close   : 0
% 21.31/12.09  
% 21.31/12.09  Ordering : KBO
% 21.31/12.09  
% 21.31/12.09  Simplification rules
% 21.31/12.09  ----------------------
% 21.31/12.09  #Subsume      : 5159
% 21.31/12.09  #Demod        : 8423
% 21.31/12.09  #Tautology    : 2812
% 21.31/12.09  #SimpNegUnit  : 5
% 21.31/12.09  #BackRed      : 32
% 21.31/12.09  
% 21.31/12.09  #Partial instantiations: 0
% 21.31/12.09  #Strategies tried      : 1
% 21.31/12.09  
% 21.31/12.09  Timing (in seconds)
% 21.31/12.09  ----------------------
% 21.31/12.09  Preprocessing        : 0.36
% 21.31/12.09  Parsing              : 0.19
% 21.31/12.09  CNF conversion       : 0.03
% 21.31/12.09  Main loop            : 10.92
% 21.31/12.09  Inferencing          : 1.71
% 21.31/12.09  Reduction            : 5.69
% 21.31/12.09  Demodulation         : 5.17
% 21.31/12.09  BG Simplification    : 0.25
% 21.31/12.09  Subsumption          : 2.75
% 21.31/12.09  Abstraction          : 0.39
% 21.31/12.10  MUC search           : 0.00
% 21.31/12.10  Cooper               : 0.00
% 21.31/12.10  Total                : 11.33
% 21.31/12.10  Index Insertion      : 0.00
% 21.31/12.10  Index Deletion       : 0.00
% 21.31/12.10  Index Matching       : 0.00
% 21.31/12.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
