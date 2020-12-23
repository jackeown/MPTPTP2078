%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:09 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 292 expanded)
%              Number of leaves         :   25 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  217 (1520 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_24,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78,plain,(
    ! [B_62,A_63,C_64] :
      ( r2_hidden(B_62,k1_tops_1(A_63,C_64))
      | ~ m1_connsp_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_62,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,(
    ! [B_62] :
      ( r2_hidden(B_62,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_78])).

tff(c_86,plain,(
    ! [B_62] :
      ( r2_hidden(B_62,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_82])).

tff(c_88,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_86])).

tff(c_10,plain,(
    ! [A_5,B_12,C_13] :
      ( r1_tarski('#skF_2'(A_5,B_12,C_13),C_13)
      | ~ r2_hidden(B_12,k1_tops_1(A_5,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [B_65] :
      ( r1_tarski('#skF_2'('#skF_3',B_65,'#skF_5'),'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_101,plain,(
    ! [B_65] :
      ( r1_tarski('#skF_2'('#skF_3',B_65,'#skF_5'),'#skF_5')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_92])).

tff(c_87,plain,(
    ! [B_62] :
      ( r2_hidden(B_62,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_62)
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_86])).

tff(c_8,plain,(
    ! [B_12,A_5,C_13] :
      ( r2_hidden(B_12,'#skF_2'(A_5,B_12,C_13))
      | ~ r2_hidden(B_12,k1_tops_1(A_5,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_2'('#skF_3',B_65,'#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_connsp_2('#skF_5','#skF_3',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_88,c_8])).

tff(c_105,plain,(
    ! [B_67] :
      ( r2_hidden(B_67,'#skF_2'('#skF_3',B_67,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_67)
      | ~ m1_subset_1(B_67,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_90])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_68] :
      ( ~ v1_xboole_0('#skF_2'('#skF_3',B_68,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_113,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_116,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_98,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_2'('#skF_3',B_65,'#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_90])).

tff(c_49,plain,(
    ! [A_47,B_48,C_49] :
      ( v3_pre_topc('#skF_2'(A_47,B_48,C_49),A_47)
      | ~ r2_hidden(B_48,k1_tops_1(A_47,C_49))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    ! [B_48] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_48,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_48,k1_tops_1('#skF_3','#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_54,plain,(
    ! [B_48] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_48,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_48,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_51])).

tff(c_14,plain,(
    ! [A_5,B_12,C_13] :
      ( m1_subset_1('#skF_2'(A_5,B_12,C_13),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ r2_hidden(B_12,k1_tops_1(A_5,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [B_72,A_73,C_74] :
      ( m1_connsp_2(B_72,A_73,C_74)
      | ~ r2_hidden(C_74,B_72)
      | ~ v3_pre_topc(B_72,A_73)
      | ~ m1_subset_1(C_74,u1_struct_0(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_130,plain,(
    ! [B_72] :
      ( m1_connsp_2(B_72,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_72)
      | ~ v3_pre_topc(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_128])).

tff(c_133,plain,(
    ! [B_72] :
      ( m1_connsp_2(B_72,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_72)
      | ~ v3_pre_topc(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_130])).

tff(c_135,plain,(
    ! [B_75] :
      ( m1_connsp_2(B_75,'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4',B_75)
      | ~ v3_pre_topc(B_75,'#skF_3')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_133])).

tff(c_139,plain,(
    ! [B_12,C_13] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_12,C_13),'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_12,C_13))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_12,C_13),'#skF_3')
      | ~ r2_hidden(B_12,k1_tops_1('#skF_3',C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_194,plain,(
    ! [B_98,C_99] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_98,C_99),'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_98,C_99))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_98,C_99),'#skF_3')
      | ~ r2_hidden(B_98,k1_tops_1('#skF_3',C_99))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_139])).

tff(c_204,plain,(
    ! [B_100] :
      ( m1_connsp_2('#skF_2'('#skF_3',B_100,'#skF_5'),'#skF_3','#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_100,'#skF_5'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_100,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_100,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_66,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1('#skF_2'(A_57,B_58,C_59),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ r2_hidden(B_58,k1_tops_1(A_57,C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [D_42] :
      ( ~ r1_tarski(D_42,'#skF_5')
      | ~ v3_pre_topc(D_42,'#skF_3')
      | ~ m1_connsp_2(D_42,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ! [B_58,C_59] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_58,C_59),'#skF_5')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_58,C_59),'#skF_3')
      | ~ m1_connsp_2('#skF_2'('#skF_3',B_58,C_59),'#skF_3','#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3',B_58,C_59))
      | ~ r2_hidden(B_58,k1_tops_1('#skF_3',C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_66,c_22])).

tff(c_76,plain,(
    ! [B_58,C_59] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_58,C_59),'#skF_5')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_58,C_59),'#skF_3')
      | ~ m1_connsp_2('#skF_2'('#skF_3',B_58,C_59),'#skF_3','#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3',B_58,C_59))
      | ~ r2_hidden(B_58,k1_tops_1('#skF_3',C_59))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_72])).

tff(c_206,plain,(
    ! [B_100] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_100,'#skF_5'),'#skF_5')
      | v1_xboole_0('#skF_2'('#skF_3',B_100,'#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_100,'#skF_5'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_100,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_100,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_204,c_76])).

tff(c_210,plain,(
    ! [B_101] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_101,'#skF_5'),'#skF_5')
      | v1_xboole_0('#skF_2'('#skF_3',B_101,'#skF_5'))
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_101,'#skF_5'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_101,'#skF_5'),'#skF_3')
      | ~ r2_hidden(B_101,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_216,plain,(
    ! [B_105] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_105,'#skF_5'),'#skF_5')
      | v1_xboole_0('#skF_2'('#skF_3',B_105,'#skF_5'))
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3',B_105,'#skF_5'))
      | ~ r2_hidden(B_105,k1_tops_1('#skF_3','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_219,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_98,c_216])).

tff(c_222,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_219])).

tff(c_223,plain,
    ( ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_222])).

tff(c_224,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_227,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_87,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_227])).

tff(c_232,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_259,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_101,c_232])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.38/1.28  
% 2.38/1.28  %Foreground sorts:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Background operators:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Foreground operators:
% 2.38/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.38/1.28  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.38/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.28  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.38/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.38/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.28  
% 2.38/1.30  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.38/1.30  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.38/1.30  tff(f_49, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 2.38/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/1.30  tff(f_85, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.38/1.30  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_24, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_32, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_78, plain, (![B_62, A_63, C_64]: (r2_hidden(B_62, k1_tops_1(A_63, C_64)) | ~m1_connsp_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_62, u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.38/1.30  tff(c_82, plain, (![B_62]: (r2_hidden(B_62, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_78])).
% 2.38/1.30  tff(c_86, plain, (![B_62]: (r2_hidden(B_62, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_82])).
% 2.38/1.30  tff(c_88, plain, (![B_65]: (r2_hidden(B_65, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_86])).
% 2.38/1.30  tff(c_10, plain, (![A_5, B_12, C_13]: (r1_tarski('#skF_2'(A_5, B_12, C_13), C_13) | ~r2_hidden(B_12, k1_tops_1(A_5, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.30  tff(c_92, plain, (![B_65]: (r1_tarski('#skF_2'('#skF_3', B_65, '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.38/1.30  tff(c_101, plain, (![B_65]: (r1_tarski('#skF_2'('#skF_3', B_65, '#skF_5'), '#skF_5') | ~m1_connsp_2('#skF_5', '#skF_3', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_92])).
% 2.38/1.30  tff(c_87, plain, (![B_62]: (r2_hidden(B_62, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_62) | ~m1_subset_1(B_62, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_34, c_86])).
% 2.38/1.30  tff(c_8, plain, (![B_12, A_5, C_13]: (r2_hidden(B_12, '#skF_2'(A_5, B_12, C_13)) | ~r2_hidden(B_12, k1_tops_1(A_5, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.30  tff(c_90, plain, (![B_65]: (r2_hidden(B_65, '#skF_2'('#skF_3', B_65, '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_connsp_2('#skF_5', '#skF_3', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_88, c_8])).
% 2.38/1.30  tff(c_105, plain, (![B_67]: (r2_hidden(B_67, '#skF_2'('#skF_3', B_67, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_67) | ~m1_subset_1(B_67, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_90])).
% 2.38/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.30  tff(c_110, plain, (![B_68]: (~v1_xboole_0('#skF_2'('#skF_3', B_68, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_68) | ~m1_subset_1(B_68, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_105, c_2])).
% 2.38/1.30  tff(c_113, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_110])).
% 2.38/1.30  tff(c_116, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_113])).
% 2.38/1.30  tff(c_98, plain, (![B_65]: (r2_hidden(B_65, '#skF_2'('#skF_3', B_65, '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_65) | ~m1_subset_1(B_65, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_90])).
% 2.38/1.30  tff(c_49, plain, (![A_47, B_48, C_49]: (v3_pre_topc('#skF_2'(A_47, B_48, C_49), A_47) | ~r2_hidden(B_48, k1_tops_1(A_47, C_49)) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.30  tff(c_51, plain, (![B_48]: (v3_pre_topc('#skF_2'('#skF_3', B_48, '#skF_5'), '#skF_3') | ~r2_hidden(B_48, k1_tops_1('#skF_3', '#skF_5')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.38/1.30  tff(c_54, plain, (![B_48]: (v3_pre_topc('#skF_2'('#skF_3', B_48, '#skF_5'), '#skF_3') | ~r2_hidden(B_48, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_51])).
% 2.38/1.30  tff(c_14, plain, (![A_5, B_12, C_13]: (m1_subset_1('#skF_2'(A_5, B_12, C_13), k1_zfmisc_1(u1_struct_0(A_5))) | ~r2_hidden(B_12, k1_tops_1(A_5, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.30  tff(c_128, plain, (![B_72, A_73, C_74]: (m1_connsp_2(B_72, A_73, C_74) | ~r2_hidden(C_74, B_72) | ~v3_pre_topc(B_72, A_73) | ~m1_subset_1(C_74, u1_struct_0(A_73)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.38/1.30  tff(c_130, plain, (![B_72]: (m1_connsp_2(B_72, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_72) | ~v3_pre_topc(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_128])).
% 2.38/1.30  tff(c_133, plain, (![B_72]: (m1_connsp_2(B_72, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_72) | ~v3_pre_topc(B_72, '#skF_3') | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_130])).
% 2.38/1.30  tff(c_135, plain, (![B_75]: (m1_connsp_2(B_75, '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', B_75) | ~v3_pre_topc(B_75, '#skF_3') | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_133])).
% 2.38/1.30  tff(c_139, plain, (![B_12, C_13]: (m1_connsp_2('#skF_2'('#skF_3', B_12, C_13), '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_12, C_13)) | ~v3_pre_topc('#skF_2'('#skF_3', B_12, C_13), '#skF_3') | ~r2_hidden(B_12, k1_tops_1('#skF_3', C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_135])).
% 2.38/1.30  tff(c_194, plain, (![B_98, C_99]: (m1_connsp_2('#skF_2'('#skF_3', B_98, C_99), '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_98, C_99)) | ~v3_pre_topc('#skF_2'('#skF_3', B_98, C_99), '#skF_3') | ~r2_hidden(B_98, k1_tops_1('#skF_3', C_99)) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_139])).
% 2.38/1.30  tff(c_204, plain, (![B_100]: (m1_connsp_2('#skF_2'('#skF_3', B_100, '#skF_5'), '#skF_3', '#skF_4') | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_100, '#skF_5')) | ~v3_pre_topc('#skF_2'('#skF_3', B_100, '#skF_5'), '#skF_3') | ~r2_hidden(B_100, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_26, c_194])).
% 2.38/1.30  tff(c_66, plain, (![A_57, B_58, C_59]: (m1_subset_1('#skF_2'(A_57, B_58, C_59), k1_zfmisc_1(u1_struct_0(A_57))) | ~r2_hidden(B_58, k1_tops_1(A_57, C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.30  tff(c_22, plain, (![D_42]: (~r1_tarski(D_42, '#skF_5') | ~v3_pre_topc(D_42, '#skF_3') | ~m1_connsp_2(D_42, '#skF_3', '#skF_4') | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_42))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.38/1.30  tff(c_72, plain, (![B_58, C_59]: (~r1_tarski('#skF_2'('#skF_3', B_58, C_59), '#skF_5') | ~v3_pre_topc('#skF_2'('#skF_3', B_58, C_59), '#skF_3') | ~m1_connsp_2('#skF_2'('#skF_3', B_58, C_59), '#skF_3', '#skF_4') | v1_xboole_0('#skF_2'('#skF_3', B_58, C_59)) | ~r2_hidden(B_58, k1_tops_1('#skF_3', C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_66, c_22])).
% 2.38/1.30  tff(c_76, plain, (![B_58, C_59]: (~r1_tarski('#skF_2'('#skF_3', B_58, C_59), '#skF_5') | ~v3_pre_topc('#skF_2'('#skF_3', B_58, C_59), '#skF_3') | ~m1_connsp_2('#skF_2'('#skF_3', B_58, C_59), '#skF_3', '#skF_4') | v1_xboole_0('#skF_2'('#skF_3', B_58, C_59)) | ~r2_hidden(B_58, k1_tops_1('#skF_3', C_59)) | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_72])).
% 2.38/1.30  tff(c_206, plain, (![B_100]: (~r1_tarski('#skF_2'('#skF_3', B_100, '#skF_5'), '#skF_5') | v1_xboole_0('#skF_2'('#skF_3', B_100, '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_100, '#skF_5')) | ~v3_pre_topc('#skF_2'('#skF_3', B_100, '#skF_5'), '#skF_3') | ~r2_hidden(B_100, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_204, c_76])).
% 2.38/1.30  tff(c_210, plain, (![B_101]: (~r1_tarski('#skF_2'('#skF_3', B_101, '#skF_5'), '#skF_5') | v1_xboole_0('#skF_2'('#skF_3', B_101, '#skF_5')) | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_101, '#skF_5')) | ~v3_pre_topc('#skF_2'('#skF_3', B_101, '#skF_5'), '#skF_3') | ~r2_hidden(B_101, k1_tops_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 2.38/1.30  tff(c_216, plain, (![B_105]: (~r1_tarski('#skF_2'('#skF_3', B_105, '#skF_5'), '#skF_5') | v1_xboole_0('#skF_2'('#skF_3', B_105, '#skF_5')) | ~r2_hidden('#skF_4', '#skF_2'('#skF_3', B_105, '#skF_5')) | ~r2_hidden(B_105, k1_tops_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_54, c_210])).
% 2.38/1.30  tff(c_219, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_98, c_216])).
% 2.38/1.30  tff(c_222, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v1_xboole_0('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_219])).
% 2.38/1.30  tff(c_223, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_116, c_222])).
% 2.38/1.30  tff(c_224, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.38/1.30  tff(c_227, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_87, c_224])).
% 2.38/1.30  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_227])).
% 2.38/1.30  tff(c_232, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_223])).
% 2.38/1.30  tff(c_259, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_232])).
% 2.38/1.30  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_259])).
% 2.38/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.30  
% 2.38/1.30  Inference rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Ref     : 0
% 2.38/1.30  #Sup     : 43
% 2.38/1.30  #Fact    : 0
% 2.38/1.30  #Define  : 0
% 2.38/1.30  #Split   : 3
% 2.38/1.30  #Chain   : 0
% 2.38/1.30  #Close   : 0
% 2.38/1.30  
% 2.38/1.30  Ordering : KBO
% 2.38/1.30  
% 2.38/1.30  Simplification rules
% 2.38/1.30  ----------------------
% 2.38/1.30  #Subsume      : 3
% 2.38/1.30  #Demod        : 42
% 2.38/1.30  #Tautology    : 3
% 2.38/1.30  #SimpNegUnit  : 5
% 2.38/1.30  #BackRed      : 0
% 2.38/1.30  
% 2.38/1.30  #Partial instantiations: 0
% 2.38/1.30  #Strategies tried      : 1
% 2.38/1.30  
% 2.38/1.30  Timing (in seconds)
% 2.38/1.30  ----------------------
% 2.38/1.30  Preprocessing        : 0.28
% 2.38/1.30  Parsing              : 0.15
% 2.38/1.30  CNF conversion       : 0.02
% 2.38/1.30  Main loop            : 0.24
% 2.38/1.30  Inferencing          : 0.10
% 2.38/1.30  Reduction            : 0.06
% 2.38/1.30  Demodulation         : 0.04
% 2.38/1.30  BG Simplification    : 0.01
% 2.38/1.30  Subsumption          : 0.04
% 2.38/1.30  Abstraction          : 0.01
% 2.38/1.30  MUC search           : 0.00
% 2.38/1.30  Cooper               : 0.00
% 2.38/1.30  Total                : 0.56
% 2.38/1.30  Index Insertion      : 0.00
% 2.38/1.30  Index Deletion       : 0.00
% 2.38/1.30  Index Matching       : 0.00
% 2.38/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
