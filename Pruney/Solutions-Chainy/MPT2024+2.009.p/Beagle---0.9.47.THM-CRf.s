%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 663 expanded)
%              Number of leaves         :   38 ( 267 expanded)
%              Depth                    :   16
%              Number of atoms          :  306 (2522 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_306,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_connsp_2(C_165,A_166,B_167)
      | ~ m1_subset_1(C_165,u1_struct_0(k9_yellow_6(A_166,B_167)))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_324,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_306])).

tff(c_334,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_324])).

tff(c_335,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_334])).

tff(c_36,plain,(
    ! [C_34,A_31,B_32] :
      ( m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_connsp_2(C_34,A_31,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_343,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_335,c_36])).

tff(c_346,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_343])).

tff(c_347,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_346])).

tff(c_379,plain,(
    ! [C_170,B_171,A_172] :
      ( r2_hidden(C_170,B_171)
      | ~ m1_connsp_2(B_171,A_172,C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(A_172))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_381,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_335,c_379])).

tff(c_386,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_347,c_54,c_381])).

tff(c_387,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_386])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k2_tarski(A_10,B_11),C_12)
      | ~ r2_hidden(B_11,C_12)
      | ~ r2_hidden(A_10,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_126,plain,(
    ! [B_87,C_88,A_89] :
      ( r2_hidden(B_87,C_88)
      | ~ r1_tarski(k2_tarski(A_89,B_87),C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,(
    ! [B_100,C_101,B_102,A_103] :
      ( r2_hidden(B_100,k2_xboole_0(C_101,B_102))
      | ~ r1_tarski(k2_tarski(A_103,B_100),B_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_164,plain,(
    ! [B_11,C_101,C_12,A_10] :
      ( r2_hidden(B_11,k2_xboole_0(C_101,C_12))
      | ~ r2_hidden(B_11,C_12)
      | ~ r2_hidden(A_10,C_12) ) ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_403,plain,(
    ! [B_11,C_101] :
      ( r2_hidden(B_11,k2_xboole_0(C_101,'#skF_5'))
      | ~ r2_hidden(B_11,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_387,c_164])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_321,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_306])).

tff(c_330,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_321])).

tff(c_331,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_330])).

tff(c_337,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_331,c_36])).

tff(c_340,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_337])).

tff(c_341,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_340])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( k4_subset_1(A_18,B_19,C_20) = k2_xboole_0(B_19,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_831,plain,(
    ! [B_219] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_219,'#skF_5') = k2_xboole_0(B_219,'#skF_5')
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_347,c_26])).

tff(c_863,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_341,c_831])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k4_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_906,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_863,c_24])).

tff(c_910,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_347,c_906])).

tff(c_741,plain,(
    ! [C_214,A_215,B_216] :
      ( r2_hidden(C_214,u1_struct_0(k9_yellow_6(A_215,B_216)))
      | ~ v3_pre_topc(C_214,A_215)
      | ~ r2_hidden(B_216,C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2569,plain,(
    ! [C_271,A_272,B_273] :
      ( m1_subset_1(C_271,u1_struct_0(k9_yellow_6(A_272,B_273)))
      | ~ v3_pre_topc(C_271,A_272)
      | ~ r2_hidden(B_273,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ m1_subset_1(B_273,u1_struct_0(A_272))
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_741,c_28])).

tff(c_48,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2578,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2569,c_48])).

tff(c_2583,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_910,c_2578])).

tff(c_2584,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2583])).

tff(c_2585,plain,(
    ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2584])).

tff(c_2588,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_403,c_2585])).

tff(c_2598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_2588])).

tff(c_2599,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2584])).

tff(c_73,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_109,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_447,plain,(
    ! [C_175,A_176,B_177] :
      ( v3_pre_topc(C_175,A_176)
      | ~ r2_hidden(C_175,u1_struct_0(k9_yellow_6(A_176,B_177)))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2954,plain,(
    ! [A_283,A_284,B_285] :
      ( v3_pre_topc(A_283,A_284)
      | ~ m1_subset_1(A_283,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ m1_subset_1(B_285,u1_struct_0(A_284))
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_284,B_285)))
      | ~ m1_subset_1(A_283,u1_struct_0(k9_yellow_6(A_284,B_285))) ) ),
    inference(resolution,[status(thm)],[c_30,c_447])).

tff(c_2972,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_52,c_2954])).

tff(c_2982,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_341,c_2972])).

tff(c_2983,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_60,c_2982])).

tff(c_2975,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_2954])).

tff(c_2986,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_347,c_2975])).

tff(c_2987,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_60,c_2986])).

tff(c_565,plain,(
    ! [B_208,C_209,A_210] :
      ( v3_pre_topc(k2_xboole_0(B_208,C_209),A_210)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ v3_pre_topc(C_209,A_210)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ v3_pre_topc(B_208,A_210)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_567,plain,(
    ! [B_208] :
      ( v3_pre_topc(k2_xboole_0(B_208,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_208,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_347,c_565])).

tff(c_584,plain,(
    ! [B_208] :
      ( v3_pre_topc(k2_xboole_0(B_208,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_208,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_567])).

tff(c_3697,plain,(
    ! [B_310] :
      ( v3_pre_topc(k2_xboole_0(B_310,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_310,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_584])).

tff(c_3763,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_341,c_3697])).

tff(c_3805,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2983,c_3763])).

tff(c_3807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2599,c_3805])).

tff(c_3808,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_4000,plain,(
    ! [C_393,A_394,B_395] :
      ( m1_connsp_2(C_393,A_394,B_395)
      | ~ m1_subset_1(C_393,u1_struct_0(k9_yellow_6(A_394,B_395)))
      | ~ m1_subset_1(B_395,u1_struct_0(A_394))
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4018,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_4000])).

tff(c_4028,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_4018])).

tff(c_4029,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4028])).

tff(c_4037,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4029,c_36])).

tff(c_4040,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_4037])).

tff(c_4041,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4040])).

tff(c_4069,plain,(
    ! [C_397,B_398,A_399] :
      ( r2_hidden(C_397,B_398)
      | ~ m1_connsp_2(B_398,A_399,C_397)
      | ~ m1_subset_1(C_397,u1_struct_0(A_399))
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4071,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4029,c_4069])).

tff(c_4076,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4041,c_54,c_4071])).

tff(c_4077,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4076])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4091,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4077,c_2])).

tff(c_4098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3808,c_4091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:47:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.17  
% 5.68/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.68/2.17  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.68/2.17  
% 5.68/2.17  %Foreground sorts:
% 5.68/2.17  
% 5.68/2.17  
% 5.68/2.17  %Background operators:
% 5.68/2.17  
% 5.68/2.17  
% 5.68/2.17  %Foreground operators:
% 5.68/2.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.68/2.17  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.68/2.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.68/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.68/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.68/2.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.68/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.68/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.68/2.17  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.68/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.68/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.68/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.68/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.17  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.68/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.68/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.68/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.68/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.68/2.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.68/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.68/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.17  
% 5.94/2.19  tff(f_182, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.94/2.19  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 5.94/2.19  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.94/2.19  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.94/2.19  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 5.94/2.19  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.94/2.19  tff(f_68, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.94/2.19  tff(f_62, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.94/2.19  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.94/2.19  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.94/2.19  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.94/2.19  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.94/2.19  tff(f_98, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.94/2.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.94/2.19  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_306, plain, (![C_165, A_166, B_167]: (m1_connsp_2(C_165, A_166, B_167) | ~m1_subset_1(C_165, u1_struct_0(k9_yellow_6(A_166, B_167))) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.94/2.19  tff(c_324, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_306])).
% 5.94/2.19  tff(c_334, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_324])).
% 5.94/2.19  tff(c_335, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_334])).
% 5.94/2.19  tff(c_36, plain, (![C_34, A_31, B_32]: (m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_connsp_2(C_34, A_31, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.94/2.19  tff(c_343, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_335, c_36])).
% 5.94/2.19  tff(c_346, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_343])).
% 5.94/2.19  tff(c_347, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_346])).
% 5.94/2.19  tff(c_379, plain, (![C_170, B_171, A_172]: (r2_hidden(C_170, B_171) | ~m1_connsp_2(B_171, A_172, C_170) | ~m1_subset_1(C_170, u1_struct_0(A_172)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.94/2.19  tff(c_381, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_335, c_379])).
% 5.94/2.19  tff(c_386, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_347, c_54, c_381])).
% 5.94/2.19  tff(c_387, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_386])).
% 5.94/2.19  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(k2_tarski(A_10, B_11), C_12) | ~r2_hidden(B_11, C_12) | ~r2_hidden(A_10, C_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.94/2.19  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.94/2.19  tff(c_126, plain, (![B_87, C_88, A_89]: (r2_hidden(B_87, C_88) | ~r1_tarski(k2_tarski(A_89, B_87), C_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.94/2.19  tff(c_158, plain, (![B_100, C_101, B_102, A_103]: (r2_hidden(B_100, k2_xboole_0(C_101, B_102)) | ~r1_tarski(k2_tarski(A_103, B_100), B_102))), inference(resolution, [status(thm)], [c_6, c_126])).
% 5.94/2.19  tff(c_164, plain, (![B_11, C_101, C_12, A_10]: (r2_hidden(B_11, k2_xboole_0(C_101, C_12)) | ~r2_hidden(B_11, C_12) | ~r2_hidden(A_10, C_12))), inference(resolution, [status(thm)], [c_10, c_158])).
% 5.94/2.19  tff(c_403, plain, (![B_11, C_101]: (r2_hidden(B_11, k2_xboole_0(C_101, '#skF_5')) | ~r2_hidden(B_11, '#skF_5'))), inference(resolution, [status(thm)], [c_387, c_164])).
% 5.94/2.19  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_321, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_306])).
% 5.94/2.19  tff(c_330, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_321])).
% 5.94/2.19  tff(c_331, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_330])).
% 5.94/2.19  tff(c_337, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_331, c_36])).
% 5.94/2.19  tff(c_340, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_337])).
% 5.94/2.19  tff(c_341, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_340])).
% 5.94/2.19  tff(c_26, plain, (![A_18, B_19, C_20]: (k4_subset_1(A_18, B_19, C_20)=k2_xboole_0(B_19, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.94/2.19  tff(c_831, plain, (![B_219]: (k4_subset_1(u1_struct_0('#skF_2'), B_219, '#skF_5')=k2_xboole_0(B_219, '#skF_5') | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_347, c_26])).
% 5.94/2.19  tff(c_863, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_341, c_831])).
% 5.94/2.19  tff(c_24, plain, (![A_15, B_16, C_17]: (m1_subset_1(k4_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.94/2.19  tff(c_906, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_863, c_24])).
% 5.94/2.19  tff(c_910, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_347, c_906])).
% 5.94/2.19  tff(c_741, plain, (![C_214, A_215, B_216]: (r2_hidden(C_214, u1_struct_0(k9_yellow_6(A_215, B_216))) | ~v3_pre_topc(C_214, A_215) | ~r2_hidden(B_216, C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(A_215))) | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.94/2.19  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(A_21, B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.94/2.19  tff(c_2569, plain, (![C_271, A_272, B_273]: (m1_subset_1(C_271, u1_struct_0(k9_yellow_6(A_272, B_273))) | ~v3_pre_topc(C_271, A_272) | ~r2_hidden(B_273, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(u1_struct_0(A_272))) | ~m1_subset_1(B_273, u1_struct_0(A_272)) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(resolution, [status(thm)], [c_741, c_28])).
% 5.94/2.19  tff(c_48, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.94/2.19  tff(c_2578, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2569, c_48])).
% 5.94/2.19  tff(c_2583, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_910, c_2578])).
% 5.94/2.19  tff(c_2584, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2583])).
% 5.94/2.19  tff(c_2585, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2584])).
% 5.94/2.19  tff(c_2588, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_403, c_2585])).
% 5.94/2.19  tff(c_2598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_2588])).
% 5.94/2.19  tff(c_2599, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_2584])).
% 5.94/2.19  tff(c_73, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.94/2.19  tff(c_88, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_73])).
% 5.94/2.19  tff(c_109, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_88])).
% 5.94/2.19  tff(c_30, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | v1_xboole_0(B_24) | ~m1_subset_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.94/2.19  tff(c_447, plain, (![C_175, A_176, B_177]: (v3_pre_topc(C_175, A_176) | ~r2_hidden(C_175, u1_struct_0(k9_yellow_6(A_176, B_177))) | ~m1_subset_1(C_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.94/2.19  tff(c_2954, plain, (![A_283, A_284, B_285]: (v3_pre_topc(A_283, A_284) | ~m1_subset_1(A_283, k1_zfmisc_1(u1_struct_0(A_284))) | ~m1_subset_1(B_285, u1_struct_0(A_284)) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_284, B_285))) | ~m1_subset_1(A_283, u1_struct_0(k9_yellow_6(A_284, B_285))))), inference(resolution, [status(thm)], [c_30, c_447])).
% 5.94/2.19  tff(c_2972, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_52, c_2954])).
% 5.94/2.19  tff(c_2982, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_341, c_2972])).
% 5.94/2.19  tff(c_2983, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_109, c_60, c_2982])).
% 5.94/2.19  tff(c_2975, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_2954])).
% 5.94/2.19  tff(c_2986, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_347, c_2975])).
% 5.94/2.19  tff(c_2987, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_109, c_60, c_2986])).
% 5.94/2.19  tff(c_565, plain, (![B_208, C_209, A_210]: (v3_pre_topc(k2_xboole_0(B_208, C_209), A_210) | ~m1_subset_1(C_209, k1_zfmisc_1(u1_struct_0(A_210))) | ~v3_pre_topc(C_209, A_210) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_210))) | ~v3_pre_topc(B_208, A_210) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.94/2.19  tff(c_567, plain, (![B_208]: (v3_pre_topc(k2_xboole_0(B_208, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_208, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_347, c_565])).
% 5.94/2.19  tff(c_584, plain, (![B_208]: (v3_pre_topc(k2_xboole_0(B_208, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_208, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_567])).
% 5.94/2.19  tff(c_3697, plain, (![B_310]: (v3_pre_topc(k2_xboole_0(B_310, '#skF_5'), '#skF_2') | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_310, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2987, c_584])).
% 5.94/2.19  tff(c_3763, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_341, c_3697])).
% 5.94/2.19  tff(c_3805, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2983, c_3763])).
% 5.94/2.19  tff(c_3807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2599, c_3805])).
% 5.94/2.19  tff(c_3808, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_88])).
% 5.94/2.19  tff(c_4000, plain, (![C_393, A_394, B_395]: (m1_connsp_2(C_393, A_394, B_395) | ~m1_subset_1(C_393, u1_struct_0(k9_yellow_6(A_394, B_395))) | ~m1_subset_1(B_395, u1_struct_0(A_394)) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.94/2.19  tff(c_4018, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_4000])).
% 5.94/2.19  tff(c_4028, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_4018])).
% 5.94/2.19  tff(c_4029, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_4028])).
% 5.94/2.19  tff(c_4037, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4029, c_36])).
% 5.94/2.19  tff(c_4040, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_4037])).
% 5.94/2.19  tff(c_4041, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_4040])).
% 5.94/2.19  tff(c_4069, plain, (![C_397, B_398, A_399]: (r2_hidden(C_397, B_398) | ~m1_connsp_2(B_398, A_399, C_397) | ~m1_subset_1(C_397, u1_struct_0(A_399)) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_399))) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.94/2.19  tff(c_4071, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4029, c_4069])).
% 5.94/2.19  tff(c_4076, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4041, c_54, c_4071])).
% 5.94/2.19  tff(c_4077, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_4076])).
% 5.94/2.19  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.94/2.19  tff(c_4091, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4077, c_2])).
% 5.94/2.19  tff(c_4098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3808, c_4091])).
% 5.94/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.19  
% 5.94/2.19  Inference rules
% 5.94/2.19  ----------------------
% 5.94/2.19  #Ref     : 0
% 5.94/2.19  #Sup     : 870
% 5.94/2.19  #Fact    : 0
% 5.94/2.19  #Define  : 0
% 5.94/2.19  #Split   : 10
% 5.94/2.19  #Chain   : 0
% 5.94/2.19  #Close   : 0
% 5.94/2.19  
% 5.94/2.19  Ordering : KBO
% 5.94/2.19  
% 5.94/2.19  Simplification rules
% 5.94/2.19  ----------------------
% 5.94/2.19  #Subsume      : 310
% 5.94/2.19  #Demod        : 496
% 5.94/2.19  #Tautology    : 91
% 5.94/2.19  #SimpNegUnit  : 159
% 5.94/2.19  #BackRed      : 6
% 5.94/2.19  
% 5.94/2.19  #Partial instantiations: 0
% 5.94/2.19  #Strategies tried      : 1
% 5.94/2.19  
% 5.94/2.19  Timing (in seconds)
% 5.94/2.19  ----------------------
% 5.94/2.19  Preprocessing        : 0.37
% 5.94/2.19  Parsing              : 0.21
% 5.94/2.19  CNF conversion       : 0.03
% 5.94/2.19  Main loop            : 1.01
% 5.94/2.19  Inferencing          : 0.33
% 5.94/2.19  Reduction            : 0.34
% 5.94/2.19  Demodulation         : 0.23
% 5.94/2.19  BG Simplification    : 0.03
% 5.94/2.19  Subsumption          : 0.22
% 5.94/2.19  Abstraction          : 0.04
% 5.94/2.19  MUC search           : 0.00
% 5.94/2.19  Cooper               : 0.00
% 5.94/2.19  Total                : 1.42
% 5.94/2.19  Index Insertion      : 0.00
% 5.94/2.19  Index Deletion       : 0.00
% 5.94/2.19  Index Matching       : 0.00
% 5.94/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
