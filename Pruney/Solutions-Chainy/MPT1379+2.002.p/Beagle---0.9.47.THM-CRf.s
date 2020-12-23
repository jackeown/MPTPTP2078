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
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 11.39s
% Output     : CNFRefutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 563 expanded)
%              Number of leaves         :   30 ( 214 expanded)
%              Depth                    :   18
%              Number of atoms          :  346 (2134 expanded)
%              Number of equality atoms :   29 ( 128 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( m1_connsp_2(C,A,B)
                        & m1_connsp_2(D,A,B) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => k9_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)) = k1_tops_1(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_62,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_62])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_88,plain,(
    ! [A_62,B_63,C_64] :
      ( k9_subset_1(A_62,B_63,C_64) = k3_xboole_0(B_63,C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [B_63] : k9_subset_1(u1_struct_0('#skF_3'),B_63,'#skF_6') = k3_xboole_0(B_63,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_60,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_75,plain,(
    m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_98,plain,(
    m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_75])).

tff(c_50,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_173,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_50])).

tff(c_174,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_267,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_connsp_2(C_100,A_101,B_102)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_269,plain,
    ( m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_267])).

tff(c_272,plain,
    ( m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_269])).

tff(c_273,plain,(
    m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_272])).

tff(c_650,plain,(
    ! [B_134,A_135,C_136] :
      ( r2_hidden(B_134,k1_tops_1(A_135,C_136))
      | ~ m1_connsp_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ m1_subset_1(B_134,u1_struct_0(A_135))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_652,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_273,c_650])).

tff(c_664,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_652])).

tff(c_665,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_134)
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_664])).

tff(c_803,plain,(
    ! [A_144,B_145,C_146] :
      ( k9_subset_1(u1_struct_0(A_144),k1_tops_1(A_144,B_145),k1_tops_1(A_144,C_146)) = k1_tops_1(A_144,k9_subset_1(u1_struct_0(A_144),B_145,C_146))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_130,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k1_tops_1(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( k9_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_318,plain,(
    ! [A_107,B_108,B_109] :
      ( k9_subset_1(u1_struct_0(A_107),B_108,k1_tops_1(A_107,B_109)) = k3_xboole_0(B_108,k1_tops_1(A_107,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_130,c_22])).

tff(c_327,plain,(
    ! [B_108] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_108,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_108,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_337,plain,(
    ! [B_108] : k9_subset_1(u1_struct_0('#skF_3'),B_108,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_108,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_327])).

tff(c_821,plain,(
    ! [B_145] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_145),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_145,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_337])).

tff(c_1788,plain,(
    ! [B_169] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_169),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_169,'#skF_6'))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_96,c_821])).

tff(c_1813,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_1788])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1886,plain,(
    ! [D_170] :
      ( r2_hidden(D_170,k1_tops_1('#skF_3','#skF_5'))
      | ~ r2_hidden(D_170,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1813,c_6])).

tff(c_2539,plain,(
    ! [B_185] :
      ( r2_hidden(B_185,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_185)
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_665,c_1886])).

tff(c_2542,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_2539])).

tff(c_2545,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2542])).

tff(c_32,plain,(
    ! [C_30,A_24,B_28] :
      ( m1_connsp_2(C_30,A_24,B_28)
      | ~ r2_hidden(B_28,k1_tops_1(A_24,C_30))
      | ~ m1_subset_1(C_30,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2547,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2545,c_32])).

tff(c_2550,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_2547])).

tff(c_2552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_174,c_2550])).

tff(c_2553,plain,(
    ~ m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_2614,plain,(
    ! [C_196,A_197,B_198] :
      ( m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_connsp_2(C_196,A_197,B_198)
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2618,plain,
    ( m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_2614])).

tff(c_2625,plain,
    ( m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2618])).

tff(c_2626,plain,(
    m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2625])).

tff(c_2964,plain,(
    ! [B_234,A_235,C_236] :
      ( r2_hidden(B_234,k1_tops_1(A_235,C_236))
      | ~ m1_connsp_2(C_236,A_235,B_234)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(u1_struct_0(A_235)))
      | ~ m1_subset_1(B_234,u1_struct_0(A_235))
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2966,plain,(
    ! [B_234] :
      ( r2_hidden(B_234,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_234)
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2626,c_2964])).

tff(c_2978,plain,(
    ! [B_234] :
      ( r2_hidden(B_234,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_234)
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2966])).

tff(c_2979,plain,(
    ! [B_234] :
      ( r2_hidden(B_234,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_234)
      | ~ m1_subset_1(B_234,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2978])).

tff(c_3481,plain,(
    ! [A_276,B_277,C_278] :
      ( k9_subset_1(u1_struct_0(A_276),k1_tops_1(A_276,B_277),k1_tops_1(A_276,C_278)) = k1_tops_1(A_276,k9_subset_1(u1_struct_0(A_276),B_277,C_278))
      | ~ m1_subset_1(C_278,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2704,plain,(
    ! [A_212,B_213,B_214] :
      ( k9_subset_1(u1_struct_0(A_212),B_213,k1_tops_1(A_212,B_214)) = k3_xboole_0(B_213,k1_tops_1(A_212,B_214))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_130,c_22])).

tff(c_2713,plain,(
    ! [B_213] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_213,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_213,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_2704])).

tff(c_2723,plain,(
    ! [B_213] : k9_subset_1(u1_struct_0('#skF_3'),B_213,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_213,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2713])).

tff(c_3499,plain,(
    ! [B_277] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_277),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_277,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3481,c_2723])).

tff(c_4854,plain,(
    ! [B_300] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_300),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_300,'#skF_6'))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_96,c_3499])).

tff(c_4879,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_4854])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5283,plain,(
    ! [D_306] :
      ( r2_hidden(D_306,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_306,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4879,c_4])).

tff(c_5802,plain,(
    ! [B_318] :
      ( r2_hidden(B_318,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_318)
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2979,c_5283])).

tff(c_5805,plain,
    ( r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_5802])).

tff(c_5808,plain,(
    r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5805])).

tff(c_5810,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5808,c_32])).

tff(c_5813,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_38,c_5810])).

tff(c_5815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2553,c_5813])).

tff(c_5817,plain,(
    ~ m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_5821,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_5817,c_58])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6251,plain,(
    ! [B_395,A_396,C_397] :
      ( r2_hidden(B_395,k1_tops_1(A_396,C_397))
      | ~ m1_connsp_2(C_397,A_396,B_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ m1_subset_1(B_395,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6262,plain,(
    ! [B_395,A_396,A_13] :
      ( r2_hidden(B_395,k1_tops_1(A_396,A_13))
      | ~ m1_connsp_2(A_13,A_396,B_395)
      | ~ m1_subset_1(B_395,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396)
      | ~ r1_tarski(A_13,u1_struct_0(A_396)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6251])).

tff(c_74,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_5816,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k3_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5822,plain,(
    ! [A_328,B_329,C_330] :
      ( k9_subset_1(A_328,B_329,C_330) = k3_xboole_0(B_329,C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(A_328)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5830,plain,(
    ! [B_329] : k9_subset_1(u1_struct_0('#skF_3'),B_329,'#skF_6') = k3_xboole_0(B_329,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_5822])).

tff(c_5872,plain,(
    ! [A_339,B_340] :
      ( m1_subset_1(k1_tops_1(A_339,B_340),k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ l1_pre_topc(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6073,plain,(
    ! [A_380,B_381,B_382] :
      ( k9_subset_1(u1_struct_0(A_380),B_381,k1_tops_1(A_380,B_382)) = k3_xboole_0(B_381,k1_tops_1(A_380,B_382))
      | ~ m1_subset_1(B_382,k1_zfmisc_1(u1_struct_0(A_380)))
      | ~ l1_pre_topc(A_380) ) ),
    inference(resolution,[status(thm)],[c_5872,c_22])).

tff(c_6080,plain,(
    ! [B_381] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_381,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_381,k1_tops_1('#skF_3','#skF_6'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_6073])).

tff(c_6087,plain,(
    ! [B_381] : k9_subset_1(u1_struct_0('#skF_3'),B_381,k1_tops_1('#skF_3','#skF_6')) = k3_xboole_0(B_381,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6080])).

tff(c_6931,plain,(
    ! [A_454,B_455,C_456] :
      ( k9_subset_1(u1_struct_0(A_454),k1_tops_1(A_454,B_455),k1_tops_1(A_454,C_456)) = k1_tops_1(A_454,k9_subset_1(u1_struct_0(A_454),B_455,C_456))
      | ~ m1_subset_1(C_456,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_454)))
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6960,plain,(
    ! [B_455] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_455),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k9_subset_1(u1_struct_0('#skF_3'),B_455,'#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6087,c_6931])).

tff(c_7980,plain,(
    ! [B_471] :
      ( k3_xboole_0(k1_tops_1('#skF_3',B_471),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0(B_471,'#skF_6'))
      | ~ m1_subset_1(B_471,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_5830,c_6960])).

tff(c_8001,plain,(
    k3_xboole_0(k1_tops_1('#skF_3','#skF_5'),k1_tops_1('#skF_3','#skF_6')) = k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_7980])).

tff(c_8320,plain,(
    ! [D_474] :
      ( r2_hidden(D_474,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_474,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_4])).

tff(c_8324,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6262,c_8320])).

tff(c_8455,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_8324])).

tff(c_8456,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_3','#skF_6'))
      | ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8455])).

tff(c_8665,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8456])).

tff(c_8668,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_8665])).

tff(c_8672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8668])).

tff(c_8674,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8456])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9117,plain,(
    ! [D_494] :
      ( r2_hidden(D_494,k1_tops_1('#skF_3',k3_xboole_0('#skF_5','#skF_6')))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_2])).

tff(c_9131,plain,(
    ! [D_494] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_494)
      | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_494,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_9117,c_32])).

tff(c_9155,plain,(
    ! [D_494] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_494)
      | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_494,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_9131])).

tff(c_9156,plain,(
    ! [D_494] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_494)
      | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_494,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_494,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_9155])).

tff(c_18078,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9156])).

tff(c_18081,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_18078])).

tff(c_18085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8674,c_18081])).

tff(c_20535,plain,(
    ! [D_706] :
      ( m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3',D_706)
      | ~ m1_subset_1(D_706,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_706,k1_tops_1('#skF_3','#skF_6'))
      | ~ r2_hidden(D_706,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_9156])).

tff(c_5832,plain,(
    ~ m1_connsp_2(k3_xboole_0('#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5830,c_5817])).

tff(c_20550,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20535,c_5832])).

tff(c_20565,plain,
    ( ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20550])).

tff(c_20566,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_20565])).

tff(c_20967,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6262,c_20566])).

tff(c_20973,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46,c_44,c_42,c_5816,c_20967])).

tff(c_20975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20973])).

tff(c_20976,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_20565])).

tff(c_20980,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6262,c_20976])).

tff(c_20986,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_44,c_42,c_5821,c_20980])).

tff(c_20988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.39/4.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.61  
% 11.39/4.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.61  %$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.39/4.61  
% 11.39/4.61  %Foreground sorts:
% 11.39/4.61  
% 11.39/4.61  
% 11.39/4.61  %Background operators:
% 11.39/4.61  
% 11.39/4.61  
% 11.39/4.61  %Foreground operators:
% 11.39/4.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.39/4.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 11.39/4.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.39/4.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.39/4.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.39/4.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.39/4.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.39/4.61  tff('#skF_5', type, '#skF_5': $i).
% 11.39/4.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.39/4.61  tff('#skF_6', type, '#skF_6': $i).
% 11.39/4.61  tff('#skF_3', type, '#skF_3': $i).
% 11.39/4.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.39/4.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.39/4.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.39/4.61  tff('#skF_4', type, '#skF_4': $i).
% 11.39/4.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.39/4.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.39/4.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.39/4.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.39/4.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.39/4.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.39/4.61  
% 11.57/4.63  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_connsp_2)).
% 11.57/4.63  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.57/4.63  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.57/4.63  tff(f_95, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 11.57/4.63  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 11.57/4.63  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (k9_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C)) = k1_tops_1(A, k9_subset_1(u1_struct_0(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tops_1)).
% 11.57/4.63  tff(f_52, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 11.57/4.63  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 11.57/4.63  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 11.57/4.63  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_62, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.57/4.63  tff(c_73, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_62])).
% 11.57/4.63  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_88, plain, (![A_62, B_63, C_64]: (k9_subset_1(A_62, B_63, C_64)=k3_xboole_0(B_63, C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.57/4.63  tff(c_96, plain, (![B_63]: (k9_subset_1(u1_struct_0('#skF_3'), B_63, '#skF_6')=k3_xboole_0(B_63, '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_88])).
% 11.57/4.63  tff(c_60, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_75, plain, (m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 11.57/4.63  tff(c_98, plain, (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_75])).
% 11.57/4.63  tff(c_50, plain, (~m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_173, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_50])).
% 11.57/4.63  tff(c_174, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_173])).
% 11.57/4.63  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_267, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_connsp_2(C_100, A_101, B_102) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.57/4.63  tff(c_269, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_98, c_267])).
% 11.57/4.63  tff(c_272, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_269])).
% 11.57/4.63  tff(c_273, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_272])).
% 11.57/4.63  tff(c_650, plain, (![B_134, A_135, C_136]: (r2_hidden(B_134, k1_tops_1(A_135, C_136)) | ~m1_connsp_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~m1_subset_1(B_134, u1_struct_0(A_135)) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.57/4.63  tff(c_652, plain, (![B_134]: (r2_hidden(B_134, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_134) | ~m1_subset_1(B_134, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_273, c_650])).
% 11.57/4.63  tff(c_664, plain, (![B_134]: (r2_hidden(B_134, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_134) | ~m1_subset_1(B_134, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_652])).
% 11.57/4.63  tff(c_665, plain, (![B_134]: (r2_hidden(B_134, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_134) | ~m1_subset_1(B_134, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_664])).
% 11.57/4.63  tff(c_803, plain, (![A_144, B_145, C_146]: (k9_subset_1(u1_struct_0(A_144), k1_tops_1(A_144, B_145), k1_tops_1(A_144, C_146))=k1_tops_1(A_144, k9_subset_1(u1_struct_0(A_144), B_145, C_146)) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_144))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.57/4.63  tff(c_130, plain, (![A_70, B_71]: (m1_subset_1(k1_tops_1(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.57/4.63  tff(c_22, plain, (![A_10, B_11, C_12]: (k9_subset_1(A_10, B_11, C_12)=k3_xboole_0(B_11, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.57/4.63  tff(c_318, plain, (![A_107, B_108, B_109]: (k9_subset_1(u1_struct_0(A_107), B_108, k1_tops_1(A_107, B_109))=k3_xboole_0(B_108, k1_tops_1(A_107, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_130, c_22])).
% 11.57/4.63  tff(c_327, plain, (![B_108]: (k9_subset_1(u1_struct_0('#skF_3'), B_108, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_108, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_318])).
% 11.57/4.63  tff(c_337, plain, (![B_108]: (k9_subset_1(u1_struct_0('#skF_3'), B_108, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_108, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_327])).
% 11.57/4.63  tff(c_821, plain, (![B_145]: (k3_xboole_0(k1_tops_1('#skF_3', B_145), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_145, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_803, c_337])).
% 11.57/4.63  tff(c_1788, plain, (![B_169]: (k3_xboole_0(k1_tops_1('#skF_3', B_169), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_169, '#skF_6')) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_96, c_821])).
% 11.57/4.63  tff(c_1813, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1788])).
% 11.57/4.63  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.57/4.63  tff(c_1886, plain, (![D_170]: (r2_hidden(D_170, k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden(D_170, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1813, c_6])).
% 11.57/4.63  tff(c_2539, plain, (![B_185]: (r2_hidden(B_185, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_185) | ~m1_subset_1(B_185, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_665, c_1886])).
% 11.57/4.63  tff(c_2542, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_2539])).
% 11.57/4.63  tff(c_2545, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2542])).
% 11.57/4.63  tff(c_32, plain, (![C_30, A_24, B_28]: (m1_connsp_2(C_30, A_24, B_28) | ~r2_hidden(B_28, k1_tops_1(A_24, C_30)) | ~m1_subset_1(C_30, k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.57/4.63  tff(c_2547, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2545, c_32])).
% 11.57/4.63  tff(c_2550, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_2547])).
% 11.57/4.63  tff(c_2552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_174, c_2550])).
% 11.57/4.63  tff(c_2553, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_173])).
% 11.57/4.63  tff(c_2614, plain, (![C_196, A_197, B_198]: (m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_connsp_2(C_196, A_197, B_198) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_95])).
% 11.57/4.63  tff(c_2618, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_98, c_2614])).
% 11.57/4.63  tff(c_2625, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_2618])).
% 11.57/4.63  tff(c_2626, plain, (m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2625])).
% 11.57/4.63  tff(c_2964, plain, (![B_234, A_235, C_236]: (r2_hidden(B_234, k1_tops_1(A_235, C_236)) | ~m1_connsp_2(C_236, A_235, B_234) | ~m1_subset_1(C_236, k1_zfmisc_1(u1_struct_0(A_235))) | ~m1_subset_1(B_234, u1_struct_0(A_235)) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.57/4.63  tff(c_2966, plain, (![B_234]: (r2_hidden(B_234, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_234) | ~m1_subset_1(B_234, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2626, c_2964])).
% 11.57/4.63  tff(c_2978, plain, (![B_234]: (r2_hidden(B_234, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_234) | ~m1_subset_1(B_234, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2966])).
% 11.57/4.63  tff(c_2979, plain, (![B_234]: (r2_hidden(B_234, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_234) | ~m1_subset_1(B_234, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2978])).
% 11.57/4.63  tff(c_3481, plain, (![A_276, B_277, C_278]: (k9_subset_1(u1_struct_0(A_276), k1_tops_1(A_276, B_277), k1_tops_1(A_276, C_278))=k1_tops_1(A_276, k9_subset_1(u1_struct_0(A_276), B_277, C_278)) | ~m1_subset_1(C_278, k1_zfmisc_1(u1_struct_0(A_276))) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.57/4.63  tff(c_2704, plain, (![A_212, B_213, B_214]: (k9_subset_1(u1_struct_0(A_212), B_213, k1_tops_1(A_212, B_214))=k3_xboole_0(B_213, k1_tops_1(A_212, B_214)) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(resolution, [status(thm)], [c_130, c_22])).
% 11.57/4.63  tff(c_2713, plain, (![B_213]: (k9_subset_1(u1_struct_0('#skF_3'), B_213, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_213, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_2704])).
% 11.57/4.63  tff(c_2723, plain, (![B_213]: (k9_subset_1(u1_struct_0('#skF_3'), B_213, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_213, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2713])).
% 11.57/4.63  tff(c_3499, plain, (![B_277]: (k3_xboole_0(k1_tops_1('#skF_3', B_277), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_277, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3481, c_2723])).
% 11.57/4.63  tff(c_4854, plain, (![B_300]: (k3_xboole_0(k1_tops_1('#skF_3', B_300), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_300, '#skF_6')) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_96, c_3499])).
% 11.57/4.63  tff(c_4879, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_4854])).
% 11.57/4.63  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.57/4.63  tff(c_5283, plain, (![D_306]: (r2_hidden(D_306, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_306, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_4879, c_4])).
% 11.57/4.63  tff(c_5802, plain, (![B_318]: (r2_hidden(B_318, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_318) | ~m1_subset_1(B_318, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2979, c_5283])).
% 11.57/4.63  tff(c_5805, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_5802])).
% 11.57/4.63  tff(c_5808, plain, (r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5805])).
% 11.57/4.63  tff(c_5810, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_5808, c_32])).
% 11.57/4.63  tff(c_5813, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_38, c_5810])).
% 11.57/4.63  tff(c_5815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2553, c_5813])).
% 11.57/4.63  tff(c_5817, plain, (~m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 11.57/4.63  tff(c_58, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | m1_connsp_2(k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.57/4.63  tff(c_5821, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_5817, c_58])).
% 11.57/4.63  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.57/4.63  tff(c_6251, plain, (![B_395, A_396, C_397]: (r2_hidden(B_395, k1_tops_1(A_396, C_397)) | ~m1_connsp_2(C_397, A_396, B_395) | ~m1_subset_1(C_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~m1_subset_1(B_395, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.57/4.63  tff(c_6262, plain, (![B_395, A_396, A_13]: (r2_hidden(B_395, k1_tops_1(A_396, A_13)) | ~m1_connsp_2(A_13, A_396, B_395) | ~m1_subset_1(B_395, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396) | ~r1_tarski(A_13, u1_struct_0(A_396)))), inference(resolution, [status(thm)], [c_26, c_6251])).
% 11.57/4.63  tff(c_74, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_62])).
% 11.57/4.63  tff(c_5816, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 11.57/4.63  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(k3_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.57/4.63  tff(c_5822, plain, (![A_328, B_329, C_330]: (k9_subset_1(A_328, B_329, C_330)=k3_xboole_0(B_329, C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(A_328)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.57/4.63  tff(c_5830, plain, (![B_329]: (k9_subset_1(u1_struct_0('#skF_3'), B_329, '#skF_6')=k3_xboole_0(B_329, '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_5822])).
% 11.57/4.63  tff(c_5872, plain, (![A_339, B_340]: (m1_subset_1(k1_tops_1(A_339, B_340), k1_zfmisc_1(u1_struct_0(A_339))) | ~m1_subset_1(B_340, k1_zfmisc_1(u1_struct_0(A_339))) | ~l1_pre_topc(A_339))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.57/4.63  tff(c_6073, plain, (![A_380, B_381, B_382]: (k9_subset_1(u1_struct_0(A_380), B_381, k1_tops_1(A_380, B_382))=k3_xboole_0(B_381, k1_tops_1(A_380, B_382)) | ~m1_subset_1(B_382, k1_zfmisc_1(u1_struct_0(A_380))) | ~l1_pre_topc(A_380))), inference(resolution, [status(thm)], [c_5872, c_22])).
% 11.57/4.63  tff(c_6080, plain, (![B_381]: (k9_subset_1(u1_struct_0('#skF_3'), B_381, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_381, k1_tops_1('#skF_3', '#skF_6')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_6073])).
% 11.57/4.63  tff(c_6087, plain, (![B_381]: (k9_subset_1(u1_struct_0('#skF_3'), B_381, k1_tops_1('#skF_3', '#skF_6'))=k3_xboole_0(B_381, k1_tops_1('#skF_3', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6080])).
% 11.57/4.63  tff(c_6931, plain, (![A_454, B_455, C_456]: (k9_subset_1(u1_struct_0(A_454), k1_tops_1(A_454, B_455), k1_tops_1(A_454, C_456))=k1_tops_1(A_454, k9_subset_1(u1_struct_0(A_454), B_455, C_456)) | ~m1_subset_1(C_456, k1_zfmisc_1(u1_struct_0(A_454))) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_454))) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.57/4.63  tff(c_6960, plain, (![B_455]: (k3_xboole_0(k1_tops_1('#skF_3', B_455), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k9_subset_1(u1_struct_0('#skF_3'), B_455, '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6087, c_6931])).
% 11.57/4.63  tff(c_7980, plain, (![B_471]: (k3_xboole_0(k1_tops_1('#skF_3', B_471), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0(B_471, '#skF_6')) | ~m1_subset_1(B_471, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_5830, c_6960])).
% 11.57/4.63  tff(c_8001, plain, (k3_xboole_0(k1_tops_1('#skF_3', '#skF_5'), k1_tops_1('#skF_3', '#skF_6'))=k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_7980])).
% 11.57/4.63  tff(c_8320, plain, (![D_474]: (r2_hidden(D_474, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_474, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_4])).
% 11.57/4.63  tff(c_8324, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6262, c_8320])).
% 11.57/4.63  tff(c_8455, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_8324])).
% 11.57/4.63  tff(c_8456, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_3', '#skF_6')) | ~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_3')) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_8455])).
% 11.57/4.63  tff(c_8665, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_8456])).
% 11.57/4.63  tff(c_8668, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_8665])).
% 11.57/4.63  tff(c_8672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_8668])).
% 11.57/4.63  tff(c_8674, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_8456])).
% 11.57/4.63  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.57/4.63  tff(c_9117, plain, (![D_494]: (r2_hidden(D_494, k1_tops_1('#skF_3', k3_xboole_0('#skF_5', '#skF_6'))) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_2])).
% 11.57/4.63  tff(c_9131, plain, (![D_494]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_494) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_494, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_9117, c_32])).
% 11.57/4.63  tff(c_9155, plain, (![D_494]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_494) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_494, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_9131])).
% 11.57/4.63  tff(c_9156, plain, (![D_494]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_494) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_494, u1_struct_0('#skF_3')) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_494, k1_tops_1('#skF_3', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_48, c_9155])).
% 11.57/4.63  tff(c_18078, plain, (~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_9156])).
% 11.57/4.63  tff(c_18081, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_18078])).
% 11.57/4.63  tff(c_18085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8674, c_18081])).
% 11.57/4.63  tff(c_20535, plain, (![D_706]: (m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', D_706) | ~m1_subset_1(D_706, u1_struct_0('#skF_3')) | ~r2_hidden(D_706, k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden(D_706, k1_tops_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_9156])).
% 11.57/4.63  tff(c_5832, plain, (~m1_connsp_2(k3_xboole_0('#skF_5', '#skF_6'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5830, c_5817])).
% 11.57/4.63  tff(c_20550, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_20535, c_5832])).
% 11.57/4.63  tff(c_20565, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20550])).
% 11.57/4.63  tff(c_20566, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_20565])).
% 11.57/4.63  tff(c_20967, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6262, c_20566])).
% 11.57/4.63  tff(c_20973, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46, c_44, c_42, c_5816, c_20967])).
% 11.57/4.63  tff(c_20975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_20973])).
% 11.57/4.63  tff(c_20976, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_6'))), inference(splitRight, [status(thm)], [c_20565])).
% 11.57/4.63  tff(c_20980, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6262, c_20976])).
% 11.57/4.63  tff(c_20986, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_44, c_42, c_5821, c_20980])).
% 11.57/4.63  tff(c_20988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_20986])).
% 11.57/4.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.57/4.63  
% 11.57/4.63  Inference rules
% 11.57/4.63  ----------------------
% 11.57/4.63  #Ref     : 0
% 11.57/4.63  #Sup     : 4578
% 11.57/4.63  #Fact    : 0
% 11.57/4.63  #Define  : 0
% 11.57/4.63  #Split   : 12
% 11.57/4.63  #Chain   : 0
% 11.57/4.63  #Close   : 0
% 11.57/4.63  
% 11.57/4.63  Ordering : KBO
% 11.57/4.63  
% 11.57/4.63  Simplification rules
% 11.57/4.63  ----------------------
% 11.57/4.63  #Subsume      : 328
% 11.57/4.63  #Demod        : 2693
% 11.57/4.63  #Tautology    : 375
% 11.57/4.63  #SimpNegUnit  : 77
% 11.57/4.63  #BackRed      : 2
% 11.57/4.63  
% 11.57/4.63  #Partial instantiations: 0
% 11.57/4.63  #Strategies tried      : 1
% 11.57/4.63  
% 11.57/4.63  Timing (in seconds)
% 11.57/4.63  ----------------------
% 11.57/4.64  Preprocessing        : 0.36
% 11.57/4.64  Parsing              : 0.18
% 11.57/4.64  CNF conversion       : 0.03
% 11.57/4.64  Main loop            : 3.55
% 11.57/4.64  Inferencing          : 0.90
% 11.57/4.64  Reduction            : 1.05
% 11.57/4.64  Demodulation         : 0.78
% 11.57/4.64  BG Simplification    : 0.15
% 11.57/4.64  Subsumption          : 1.20
% 11.57/4.64  Abstraction          : 0.22
% 11.57/4.64  MUC search           : 0.00
% 11.57/4.64  Cooper               : 0.00
% 11.57/4.64  Total                : 3.95
% 11.57/4.64  Index Insertion      : 0.00
% 11.57/4.64  Index Deletion       : 0.00
% 11.57/4.64  Index Matching       : 0.00
% 11.57/4.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
