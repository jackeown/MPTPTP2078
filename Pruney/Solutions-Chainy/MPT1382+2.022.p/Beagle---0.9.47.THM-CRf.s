%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:10 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 250 expanded)
%              Number of leaves         :   26 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 (1034 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_36,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_24,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_439,plain,(
    ! [B_84,A_85,C_86] :
      ( r2_hidden(B_84,k1_tops_1(A_85,C_86))
      | ~ m1_connsp_2(C_86,A_85,B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_84,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_448,plain,(
    ! [B_84,A_85,A_1] :
      ( r2_hidden(B_84,k1_tops_1(A_85,A_1))
      | ~ m1_connsp_2(A_1,A_85,B_84)
      | ~ m1_subset_1(B_84,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85)
      | ~ r1_tarski(A_1,u1_struct_0(A_85)) ) ),
    inference(resolution,[status(thm)],[c_4,c_439])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_130,plain,(
    ! [A_62,B_63] :
      ( k1_tops_1(A_62,k1_tops_1(A_62,B_63)) = k1_tops_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,
    ( k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_130])).

tff(c_142,plain,(
    k1_tops_1('#skF_1',k1_tops_1('#skF_1','#skF_3')) = k1_tops_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_137])).

tff(c_519,plain,(
    ! [C_94,A_95,B_96] :
      ( m1_connsp_2(C_94,A_95,B_96)
      | ~ r2_hidden(B_96,k1_tops_1(A_95,C_94))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_529,plain,(
    ! [B_96] :
      ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_96)
      | ~ r2_hidden(B_96,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_519])).

tff(c_536,plain,(
    ! [B_96] :
      ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_96)
      | ~ r2_hidden(B_96,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_529])).

tff(c_537,plain,(
    ! [B_96] :
      ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_96)
      | ~ r2_hidden(B_96,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_536])).

tff(c_538,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_541,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_538])).

tff(c_548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_541])).

tff(c_599,plain,(
    ! [B_97] :
      ( m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1',B_97)
      | ~ r2_hidden(B_97,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_90,plain,(
    ! [A_54,B_55] :
      ( v3_pre_topc(k1_tops_1(A_54,B_55),A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_95,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_99,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_95])).

tff(c_66,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tops_1(A_46,B_47),B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_75,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_101,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k1_tops_1(A_58,B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_22,plain,(
    ! [D_37] :
      ( ~ r1_tarski(D_37,'#skF_3')
      | ~ v3_pre_topc(D_37,'#skF_1')
      | ~ m1_connsp_2(D_37,'#skF_1','#skF_2')
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v1_xboole_0(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_111,plain,(
    ! [B_59] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_59),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_59),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_59),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_101,c_22])).

tff(c_177,plain,(
    ! [B_64] :
      ( ~ r1_tarski(k1_tops_1('#skF_1',B_64),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_64),'#skF_1')
      | ~ m1_connsp_2(k1_tops_1('#skF_1',B_64),'#skF_1','#skF_2')
      | v1_xboole_0(k1_tops_1('#skF_1',B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_111])).

tff(c_188,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_177])).

tff(c_195,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_75,c_188])).

tff(c_202,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_1','#skF_3'),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_607,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_599,c_202])).

tff(c_615,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_607])).

tff(c_618,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_448,c_615])).

tff(c_624,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_32,c_30,c_28,c_24,c_618])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_624])).

tff(c_627,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tops_1(A_58,B_59),u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_72,plain,(
    ! [A_46,A_1] :
      ( r1_tarski(k1_tops_1(A_46,A_1),A_1)
      | ~ l1_pre_topc(A_46)
      | ~ r1_tarski(A_1,u1_struct_0(A_46)) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_155,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_72])).

tff(c_165,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_155])).

tff(c_167,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_170,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_121,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_170])).

tff(c_175,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_913,plain,(
    ! [B_117,A_118,C_119] :
      ( r2_hidden(B_117,k1_tops_1(A_118,C_119))
      | ~ m1_connsp_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_117,u1_struct_0(A_118))
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_922,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_913])).

tff(c_931,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_117)
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_922])).

tff(c_933,plain,(
    ! [B_120] :
      ( r2_hidden(B_120,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_931])).

tff(c_58,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [B_2,A_45,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_45,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_941,plain,(
    ! [B_2,B_120] :
      ( ~ v1_xboole_0(B_2)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_2)
      | ~ m1_connsp_2('#skF_3','#skF_1',B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_933,c_63])).

tff(c_943,plain,(
    ! [B_121] :
      ( ~ m1_connsp_2('#skF_3','#skF_1',B_121)
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_1')) ) ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_946,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_943])).

tff(c_950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_946])).

tff(c_967,plain,(
    ! [B_123] :
      ( ~ v1_xboole_0(B_123)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_123) ) ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_970,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_175,c_967])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.51  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.07/1.51  
% 3.07/1.51  %Foreground sorts:
% 3.07/1.51  
% 3.07/1.51  
% 3.07/1.51  %Background operators:
% 3.07/1.51  
% 3.07/1.51  
% 3.07/1.51  %Foreground operators:
% 3.07/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.07/1.51  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.07/1.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.07/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.51  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.07/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.07/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.07/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.51  
% 3.35/1.53  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.35/1.53  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.35/1.53  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.35/1.53  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 3.35/1.53  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 3.35/1.53  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.35/1.53  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.35/1.53  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.35/1.53  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_36, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.53  tff(c_44, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_36])).
% 3.35/1.53  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_24, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.53  tff(c_439, plain, (![B_84, A_85, C_86]: (r2_hidden(B_84, k1_tops_1(A_85, C_86)) | ~m1_connsp_2(C_86, A_85, B_84) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_84, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.53  tff(c_448, plain, (![B_84, A_85, A_1]: (r2_hidden(B_84, k1_tops_1(A_85, A_1)) | ~m1_connsp_2(A_1, A_85, B_84) | ~m1_subset_1(B_84, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85) | ~r1_tarski(A_1, u1_struct_0(A_85)))), inference(resolution, [status(thm)], [c_4, c_439])).
% 3.35/1.53  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.53  tff(c_130, plain, (![A_62, B_63]: (k1_tops_1(A_62, k1_tops_1(A_62, B_63))=k1_tops_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.35/1.53  tff(c_137, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_130])).
% 3.35/1.53  tff(c_142, plain, (k1_tops_1('#skF_1', k1_tops_1('#skF_1', '#skF_3'))=k1_tops_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_137])).
% 3.35/1.53  tff(c_519, plain, (![C_94, A_95, B_96]: (m1_connsp_2(C_94, A_95, B_96) | ~r2_hidden(B_96, k1_tops_1(A_95, C_94)) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.53  tff(c_529, plain, (![B_96]: (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_96) | ~r2_hidden(B_96, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_519])).
% 3.35/1.53  tff(c_536, plain, (![B_96]: (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_96) | ~r2_hidden(B_96, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_529])).
% 3.35/1.53  tff(c_537, plain, (![B_96]: (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_96) | ~r2_hidden(B_96, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_536])).
% 3.35/1.53  tff(c_538, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_537])).
% 3.35/1.53  tff(c_541, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_538])).
% 3.35/1.53  tff(c_548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_541])).
% 3.35/1.53  tff(c_599, plain, (![B_97]: (m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', B_97) | ~r2_hidden(B_97, k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(B_97, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_537])).
% 3.35/1.53  tff(c_90, plain, (![A_54, B_55]: (v3_pre_topc(k1_tops_1(A_54, B_55), A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.35/1.53  tff(c_95, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_90])).
% 3.35/1.53  tff(c_99, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_95])).
% 3.35/1.53  tff(c_66, plain, (![A_46, B_47]: (r1_tarski(k1_tops_1(A_46, B_47), B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.35/1.53  tff(c_71, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_66])).
% 3.35/1.53  tff(c_75, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_71])).
% 3.35/1.53  tff(c_101, plain, (![A_58, B_59]: (m1_subset_1(k1_tops_1(A_58, B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.35/1.53  tff(c_22, plain, (![D_37]: (~r1_tarski(D_37, '#skF_3') | ~v3_pre_topc(D_37, '#skF_1') | ~m1_connsp_2(D_37, '#skF_1', '#skF_2') | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(D_37))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.35/1.53  tff(c_111, plain, (![B_59]: (~r1_tarski(k1_tops_1('#skF_1', B_59), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_59), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_59), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_101, c_22])).
% 3.35/1.53  tff(c_177, plain, (![B_64]: (~r1_tarski(k1_tops_1('#skF_1', B_64), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_64), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', B_64), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_111])).
% 3.35/1.53  tff(c_188, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_177])).
% 3.35/1.53  tff(c_195, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_75, c_188])).
% 3.35/1.53  tff(c_202, plain, (~m1_connsp_2(k1_tops_1('#skF_1', '#skF_3'), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_195])).
% 3.35/1.53  tff(c_607, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_599, c_202])).
% 3.35/1.53  tff(c_615, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_607])).
% 3.35/1.53  tff(c_618, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_448, c_615])).
% 3.35/1.53  tff(c_624, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_32, c_30, c_28, c_24, c_618])).
% 3.35/1.53  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_624])).
% 3.35/1.53  tff(c_627, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_195])).
% 3.35/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.35/1.53  tff(c_121, plain, (![A_58, B_59]: (r1_tarski(k1_tops_1(A_58, B_59), u1_struct_0(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_101, c_2])).
% 3.35/1.53  tff(c_72, plain, (![A_46, A_1]: (r1_tarski(k1_tops_1(A_46, A_1), A_1) | ~l1_pre_topc(A_46) | ~r1_tarski(A_1, u1_struct_0(A_46)))), inference(resolution, [status(thm)], [c_4, c_66])).
% 3.35/1.53  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_72])).
% 3.35/1.53  tff(c_165, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_155])).
% 3.35/1.53  tff(c_167, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_165])).
% 3.35/1.53  tff(c_170, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_121, c_167])).
% 3.35/1.53  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_170])).
% 3.35/1.53  tff(c_175, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_165])).
% 3.35/1.53  tff(c_913, plain, (![B_117, A_118, C_119]: (r2_hidden(B_117, k1_tops_1(A_118, C_119)) | ~m1_connsp_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_117, u1_struct_0(A_118)) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.35/1.53  tff(c_922, plain, (![B_117]: (r2_hidden(B_117, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_913])).
% 3.35/1.53  tff(c_931, plain, (![B_117]: (r2_hidden(B_117, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_117) | ~m1_subset_1(B_117, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_922])).
% 3.35/1.53  tff(c_933, plain, (![B_120]: (r2_hidden(B_120, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_34, c_931])).
% 3.35/1.53  tff(c_58, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.35/1.53  tff(c_63, plain, (![B_2, A_45, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_45, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_58])).
% 3.35/1.53  tff(c_941, plain, (![B_2, B_120]: (~v1_xboole_0(B_2) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_2) | ~m1_connsp_2('#skF_3', '#skF_1', B_120) | ~m1_subset_1(B_120, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_933, c_63])).
% 3.35/1.53  tff(c_943, plain, (![B_121]: (~m1_connsp_2('#skF_3', '#skF_1', B_121) | ~m1_subset_1(B_121, u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_941])).
% 3.35/1.53  tff(c_946, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_943])).
% 3.35/1.53  tff(c_950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_946])).
% 3.35/1.53  tff(c_967, plain, (![B_123]: (~v1_xboole_0(B_123) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_123))), inference(splitRight, [status(thm)], [c_941])).
% 3.35/1.53  tff(c_970, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_175, c_967])).
% 3.35/1.53  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_627, c_970])).
% 3.35/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  Inference rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Ref     : 0
% 3.35/1.53  #Sup     : 211
% 3.35/1.53  #Fact    : 0
% 3.35/1.53  #Define  : 0
% 3.35/1.53  #Split   : 7
% 3.35/1.53  #Chain   : 0
% 3.35/1.53  #Close   : 0
% 3.35/1.53  
% 3.35/1.53  Ordering : KBO
% 3.35/1.53  
% 3.35/1.53  Simplification rules
% 3.35/1.53  ----------------------
% 3.35/1.53  #Subsume      : 36
% 3.35/1.53  #Demod        : 208
% 3.35/1.53  #Tautology    : 94
% 3.35/1.53  #SimpNegUnit  : 14
% 3.35/1.53  #BackRed      : 0
% 3.35/1.53  
% 3.35/1.53  #Partial instantiations: 0
% 3.35/1.53  #Strategies tried      : 1
% 3.35/1.53  
% 3.35/1.53  Timing (in seconds)
% 3.35/1.53  ----------------------
% 3.35/1.54  Preprocessing        : 0.31
% 3.35/1.54  Parsing              : 0.18
% 3.35/1.54  CNF conversion       : 0.02
% 3.35/1.54  Main loop            : 0.40
% 3.35/1.54  Inferencing          : 0.16
% 3.35/1.54  Reduction            : 0.12
% 3.35/1.54  Demodulation         : 0.08
% 3.35/1.54  BG Simplification    : 0.02
% 3.35/1.54  Subsumption          : 0.08
% 3.35/1.54  Abstraction          : 0.02
% 3.35/1.54  MUC search           : 0.00
% 3.35/1.54  Cooper               : 0.00
% 3.35/1.54  Total                : 0.75
% 3.35/1.54  Index Insertion      : 0.00
% 3.35/1.54  Index Deletion       : 0.00
% 3.35/1.54  Index Matching       : 0.00
% 3.35/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
