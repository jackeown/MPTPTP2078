%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:05 EST 2020

% Result     : Theorem 16.78s
% Output     : CNFRefutation 16.96s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 190 expanded)
%              Number of leaves         :   32 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          :  264 ( 668 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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
                     => m1_connsp_2(k4_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_104,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_49,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_49])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_57,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_65,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_62] : r1_tarski(A_62,A_62) ),
    inference(resolution,[status(thm)],[c_65,c_4])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k2_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(C_11,B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_77,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_tops_1(A_71,B_72),B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_84,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_77])).

tff(c_91,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_84])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [C_65,B_66,A_67] :
      ( r2_hidden(C_65,B_66)
      | ~ r2_hidden(C_65,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(A_75,B_77)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_526,plain,(
    ! [A_115,B_116,B_117,B_118] :
      ( r2_hidden('#skF_1'(A_115,B_116),B_117)
      | ~ r1_tarski(B_118,B_117)
      | ~ r1_tarski(A_115,B_118)
      | r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_1210,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_1'(A_138,B_139),'#skF_5')
      | ~ r1_tarski(A_138,k1_tops_1('#skF_2','#skF_5'))
      | r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_91,c_526])).

tff(c_13888,plain,(
    ! [A_614,B_615,B_616] :
      ( r2_hidden('#skF_1'(A_614,B_615),B_616)
      | ~ r1_tarski('#skF_5',B_616)
      | ~ r1_tarski(A_614,k1_tops_1('#skF_2','#skF_5'))
      | r1_tarski(A_614,B_615) ) ),
    inference(resolution,[status(thm)],[c_1210,c_2])).

tff(c_13901,plain,(
    ! [B_617,A_618] :
      ( ~ r1_tarski('#skF_5',B_617)
      | ~ r1_tarski(A_618,k1_tops_1('#skF_2','#skF_5'))
      | r1_tarski(A_618,B_617) ) ),
    inference(resolution,[status(thm)],[c_13888,c_4])).

tff(c_14287,plain,(
    ! [A_621,C_622,B_623] :
      ( ~ r1_tarski(A_621,k1_tops_1('#skF_2','#skF_5'))
      | r1_tarski(A_621,k2_xboole_0(C_622,B_623))
      | ~ r1_tarski('#skF_5',B_623) ) ),
    inference(resolution,[status(thm)],[c_8,c_13901])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_110,plain,(
    ! [A_80,B_81] :
      ( v3_pre_topc(k1_tops_1(A_80,B_81),A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_119,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_127,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_119])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k1_tops_1(A_17,B_18),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_335,plain,(
    ! [B_100,A_101,C_102] :
      ( r1_tarski(B_100,k1_tops_1(A_101,C_102))
      | ~ r1_tarski(B_100,C_102)
      | ~ v3_pre_topc(B_100,A_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1519,plain,(
    ! [B_162,A_163,A_164] :
      ( r1_tarski(B_162,k1_tops_1(A_163,A_164))
      | ~ r1_tarski(B_162,A_164)
      | ~ v3_pre_topc(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163)
      | ~ r1_tarski(A_164,u1_struct_0(A_163)) ) ),
    inference(resolution,[status(thm)],[c_16,c_335])).

tff(c_1529,plain,(
    ! [A_17,B_18,A_164] :
      ( r1_tarski(k1_tops_1(A_17,B_18),k1_tops_1(A_17,A_164))
      | ~ r1_tarski(k1_tops_1(A_17,B_18),A_164)
      | ~ v3_pre_topc(k1_tops_1(A_17,B_18),A_17)
      | ~ r1_tarski(A_164,u1_struct_0(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_1519])).

tff(c_34,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_344,plain,(
    ! [B_100] :
      ( r1_tarski(B_100,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_100,'#skF_5')
      | ~ v3_pre_topc(B_100,'#skF_2')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_335])).

tff(c_499,plain,(
    ! [B_114] :
      ( r1_tarski(B_114,k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(B_114,'#skF_5')
      | ~ v3_pre_topc(B_114,'#skF_2')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_344])).

tff(c_503,plain,(
    ! [B_18] :
      ( r1_tarski(k1_tops_1('#skF_2',B_18),k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_18),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_499])).

tff(c_516,plain,(
    ! [B_18] :
      ( r1_tarski(k1_tops_1('#skF_2',B_18),k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_18),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_503])).

tff(c_626,plain,(
    ! [B_123,A_124,C_125] :
      ( r2_hidden(B_123,k1_tops_1(A_124,C_125))
      | ~ m1_connsp_2(C_125,A_124,B_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_123,u1_struct_0(A_124))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1686,plain,(
    ! [B_185,A_186,A_187] :
      ( r2_hidden(B_185,k1_tops_1(A_186,A_187))
      | ~ m1_connsp_2(A_187,A_186,B_185)
      | ~ m1_subset_1(B_185,u1_struct_0(A_186))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ r1_tarski(A_187,u1_struct_0(A_186)) ) ),
    inference(resolution,[status(thm)],[c_16,c_626])).

tff(c_8047,plain,(
    ! [B_389,B_390,A_391,A_392] :
      ( r2_hidden(B_389,B_390)
      | ~ r1_tarski(k1_tops_1(A_391,A_392),B_390)
      | ~ m1_connsp_2(A_392,A_391,B_389)
      | ~ m1_subset_1(B_389,u1_struct_0(A_391))
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391)
      | ~ r1_tarski(A_392,u1_struct_0(A_391)) ) ),
    inference(resolution,[status(thm)],[c_1686,c_2])).

tff(c_8064,plain,(
    ! [B_389,B_18] :
      ( r2_hidden(B_389,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2(B_18,'#skF_2',B_389)
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_18,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_18),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_516,c_8047])).

tff(c_8135,plain,(
    ! [B_389,B_18] :
      ( r2_hidden(B_389,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2(B_18,'#skF_2',B_389)
      | ~ m1_subset_1(B_389,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_18,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_18),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_18),'#skF_2')
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_8064])).

tff(c_8823,plain,(
    ! [B_434,B_435] :
      ( r2_hidden(B_434,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2(B_435,'#skF_2',B_434)
      | ~ m1_subset_1(B_434,u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_435,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_435),'#skF_5')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_435),'#skF_2')
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_8135])).

tff(c_8827,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_34,c_8823])).

tff(c_8833,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_127,c_91,c_57,c_42,c_8827])).

tff(c_8843,plain,(
    ! [B_436] :
      ( r2_hidden('#skF_3',B_436)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_436) ) ),
    inference(resolution,[status(thm)],[c_8833,c_2])).

tff(c_8847,plain,(
    ! [A_164] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',A_164))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_164)
      | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2')
      | ~ r1_tarski(A_164,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1529,c_8843])).

tff(c_9173,plain,(
    ! [A_447] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',A_447))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_127,c_8847])).

tff(c_26,plain,(
    ! [C_37,A_31,B_35] :
      ( m1_connsp_2(C_37,A_31,B_35)
      | ~ r2_hidden(B_35,k1_tops_1(A_31,C_37))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_35,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9175,plain,(
    ! [A_447] :
      ( m1_connsp_2(A_447,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_9173,c_26])).

tff(c_9180,plain,(
    ! [A_447] :
      ( m1_connsp_2(A_447,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_9175])).

tff(c_12840,plain,(
    ! [A_563] :
      ( m1_connsp_2(A_563,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_563,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_563)
      | ~ r1_tarski(A_563,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_9180])).

tff(c_12874,plain,(
    ! [A_15] :
      ( m1_connsp_2(A_15,'#skF_2','#skF_3')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),A_15)
      | ~ r1_tarski(A_15,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_12840])).

tff(c_14311,plain,(
    ! [C_622,B_623] :
      ( m1_connsp_2(k2_xboole_0(C_622,B_623),'#skF_2','#skF_3')
      | ~ r1_tarski(k2_xboole_0(C_622,B_623),u1_struct_0('#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),k1_tops_1('#skF_2','#skF_5'))
      | ~ r1_tarski('#skF_5',B_623) ) ),
    inference(resolution,[status(thm)],[c_14287,c_12874])).

tff(c_14570,plain,(
    ! [C_624,B_625] :
      ( m1_connsp_2(k2_xboole_0(C_624,B_625),'#skF_2','#skF_3')
      | ~ r1_tarski(k2_xboole_0(C_624,B_625),u1_struct_0('#skF_2'))
      | ~ r1_tarski('#skF_5',B_625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14311])).

tff(c_42522,plain,(
    ! [A_1202,C_1203] :
      ( m1_connsp_2(k2_xboole_0(A_1202,C_1203),'#skF_2','#skF_3')
      | ~ r1_tarski('#skF_5',C_1203)
      | ~ r1_tarski(C_1203,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1202,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_14570])).

tff(c_129,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_222,plain,(
    ! [B_94] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_94,'#skF_5') = k2_xboole_0(B_94,'#skF_5')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_241,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_222])).

tff(c_32,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_243,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_32])).

tff(c_42541,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42522,c_243])).

tff(c_42573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_57,c_70,c_42541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.78/8.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.78/8.30  
% 16.78/8.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.78/8.30  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 16.78/8.30  
% 16.78/8.30  %Foreground sorts:
% 16.78/8.30  
% 16.78/8.30  
% 16.78/8.30  %Background operators:
% 16.78/8.30  
% 16.78/8.30  
% 16.78/8.30  %Foreground operators:
% 16.78/8.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.78/8.30  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 16.78/8.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.78/8.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.78/8.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.78/8.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.78/8.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.78/8.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.78/8.30  tff('#skF_5', type, '#skF_5': $i).
% 16.78/8.30  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.78/8.30  tff('#skF_2', type, '#skF_2': $i).
% 16.78/8.30  tff('#skF_3', type, '#skF_3': $i).
% 16.78/8.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.78/8.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.78/8.30  tff('#skF_4', type, '#skF_4': $i).
% 16.78/8.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.78/8.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.78/8.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.78/8.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.78/8.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.78/8.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.78/8.30  
% 16.96/8.32  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) => m1_connsp_2(k4_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_connsp_2)).
% 16.96/8.32  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.96/8.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.96/8.32  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 16.96/8.32  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 16.96/8.32  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 16.96/8.32  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 16.96/8.32  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 16.96/8.32  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 16.96/8.32  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 16.96/8.32  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 16.96/8.32  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_49, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.96/8.32  tff(c_56, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_49])).
% 16.96/8.32  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_57, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 16.96/8.32  tff(c_65, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.96/8.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.96/8.32  tff(c_70, plain, (![A_62]: (r1_tarski(A_62, A_62))), inference(resolution, [status(thm)], [c_65, c_4])).
% 16.96/8.32  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(k2_xboole_0(A_9, C_11), B_10) | ~r1_tarski(C_11, B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.96/8.32  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.96/8.32  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_77, plain, (![A_71, B_72]: (r1_tarski(k1_tops_1(A_71, B_72), B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.96/8.32  tff(c_84, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_77])).
% 16.96/8.32  tff(c_91, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_84])).
% 16.96/8.32  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.96/8.32  tff(c_72, plain, (![C_65, B_66, A_67]: (r2_hidden(C_65, B_66) | ~r2_hidden(C_65, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.96/8.32  tff(c_93, plain, (![A_75, B_76, B_77]: (r2_hidden('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(A_75, B_77) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_6, c_72])).
% 16.96/8.32  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.96/8.32  tff(c_526, plain, (![A_115, B_116, B_117, B_118]: (r2_hidden('#skF_1'(A_115, B_116), B_117) | ~r1_tarski(B_118, B_117) | ~r1_tarski(A_115, B_118) | r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_93, c_2])).
% 16.96/8.32  tff(c_1210, plain, (![A_138, B_139]: (r2_hidden('#skF_1'(A_138, B_139), '#skF_5') | ~r1_tarski(A_138, k1_tops_1('#skF_2', '#skF_5')) | r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_91, c_526])).
% 16.96/8.32  tff(c_13888, plain, (![A_614, B_615, B_616]: (r2_hidden('#skF_1'(A_614, B_615), B_616) | ~r1_tarski('#skF_5', B_616) | ~r1_tarski(A_614, k1_tops_1('#skF_2', '#skF_5')) | r1_tarski(A_614, B_615))), inference(resolution, [status(thm)], [c_1210, c_2])).
% 16.96/8.32  tff(c_13901, plain, (![B_617, A_618]: (~r1_tarski('#skF_5', B_617) | ~r1_tarski(A_618, k1_tops_1('#skF_2', '#skF_5')) | r1_tarski(A_618, B_617))), inference(resolution, [status(thm)], [c_13888, c_4])).
% 16.96/8.32  tff(c_14287, plain, (![A_621, C_622, B_623]: (~r1_tarski(A_621, k1_tops_1('#skF_2', '#skF_5')) | r1_tarski(A_621, k2_xboole_0(C_622, B_623)) | ~r1_tarski('#skF_5', B_623))), inference(resolution, [status(thm)], [c_8, c_13901])).
% 16.96/8.32  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.96/8.32  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_110, plain, (![A_80, B_81]: (v3_pre_topc(k1_tops_1(A_80, B_81), A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.96/8.32  tff(c_119, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_110])).
% 16.96/8.32  tff(c_127, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_119])).
% 16.96/8.32  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(k1_tops_1(A_17, B_18), k1_zfmisc_1(u1_struct_0(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 16.96/8.32  tff(c_335, plain, (![B_100, A_101, C_102]: (r1_tarski(B_100, k1_tops_1(A_101, C_102)) | ~r1_tarski(B_100, C_102) | ~v3_pre_topc(B_100, A_101) | ~m1_subset_1(C_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.96/8.32  tff(c_1519, plain, (![B_162, A_163, A_164]: (r1_tarski(B_162, k1_tops_1(A_163, A_164)) | ~r1_tarski(B_162, A_164) | ~v3_pre_topc(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(A_163) | ~r1_tarski(A_164, u1_struct_0(A_163)))), inference(resolution, [status(thm)], [c_16, c_335])).
% 16.96/8.32  tff(c_1529, plain, (![A_17, B_18, A_164]: (r1_tarski(k1_tops_1(A_17, B_18), k1_tops_1(A_17, A_164)) | ~r1_tarski(k1_tops_1(A_17, B_18), A_164) | ~v3_pre_topc(k1_tops_1(A_17, B_18), A_17) | ~r1_tarski(A_164, u1_struct_0(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_18, c_1519])).
% 16.96/8.32  tff(c_34, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_344, plain, (![B_100]: (r1_tarski(B_100, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_100, '#skF_5') | ~v3_pre_topc(B_100, '#skF_2') | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_335])).
% 16.96/8.32  tff(c_499, plain, (![B_114]: (r1_tarski(B_114, k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(B_114, '#skF_5') | ~v3_pre_topc(B_114, '#skF_2') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_344])).
% 16.96/8.32  tff(c_503, plain, (![B_18]: (r1_tarski(k1_tops_1('#skF_2', B_18), k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(k1_tops_1('#skF_2', B_18), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', B_18), '#skF_2') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_499])).
% 16.96/8.32  tff(c_516, plain, (![B_18]: (r1_tarski(k1_tops_1('#skF_2', B_18), k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski(k1_tops_1('#skF_2', B_18), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', B_18), '#skF_2') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_503])).
% 16.96/8.32  tff(c_626, plain, (![B_123, A_124, C_125]: (r2_hidden(B_123, k1_tops_1(A_124, C_125)) | ~m1_connsp_2(C_125, A_124, B_123) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_123, u1_struct_0(A_124)) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.96/8.32  tff(c_1686, plain, (![B_185, A_186, A_187]: (r2_hidden(B_185, k1_tops_1(A_186, A_187)) | ~m1_connsp_2(A_187, A_186, B_185) | ~m1_subset_1(B_185, u1_struct_0(A_186)) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~r1_tarski(A_187, u1_struct_0(A_186)))), inference(resolution, [status(thm)], [c_16, c_626])).
% 16.96/8.32  tff(c_8047, plain, (![B_389, B_390, A_391, A_392]: (r2_hidden(B_389, B_390) | ~r1_tarski(k1_tops_1(A_391, A_392), B_390) | ~m1_connsp_2(A_392, A_391, B_389) | ~m1_subset_1(B_389, u1_struct_0(A_391)) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391) | ~r1_tarski(A_392, u1_struct_0(A_391)))), inference(resolution, [status(thm)], [c_1686, c_2])).
% 16.96/8.32  tff(c_8064, plain, (![B_389, B_18]: (r2_hidden(B_389, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2(B_18, '#skF_2', B_389) | ~m1_subset_1(B_389, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_18, u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', B_18), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', B_18), '#skF_2') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_516, c_8047])).
% 16.96/8.32  tff(c_8135, plain, (![B_389, B_18]: (r2_hidden(B_389, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2(B_18, '#skF_2', B_389) | ~m1_subset_1(B_389, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_18, u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', B_18), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', B_18), '#skF_2') | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_8064])).
% 16.96/8.32  tff(c_8823, plain, (![B_434, B_435]: (r2_hidden(B_434, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2(B_435, '#skF_2', B_434) | ~m1_subset_1(B_434, u1_struct_0('#skF_2')) | ~r1_tarski(B_435, u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', B_435), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', B_435), '#skF_2') | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_8135])).
% 16.96/8.32  tff(c_8827, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_8823])).
% 16.96/8.32  tff(c_8833, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_127, c_91, c_57, c_42, c_8827])).
% 16.96/8.32  tff(c_8843, plain, (![B_436]: (r2_hidden('#skF_3', B_436) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_436))), inference(resolution, [status(thm)], [c_8833, c_2])).
% 16.96/8.32  tff(c_8847, plain, (![A_164]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', A_164)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_164) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2') | ~r1_tarski(A_164, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1529, c_8843])).
% 16.96/8.32  tff(c_9173, plain, (![A_447]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', A_447)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_127, c_8847])).
% 16.96/8.32  tff(c_26, plain, (![C_37, A_31, B_35]: (m1_connsp_2(C_37, A_31, B_35) | ~r2_hidden(B_35, k1_tops_1(A_31, C_37)) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_35, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 16.96/8.32  tff(c_9175, plain, (![A_447]: (m1_connsp_2(A_447, '#skF_2', '#skF_3') | ~m1_subset_1(A_447, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_9173, c_26])).
% 16.96/8.32  tff(c_9180, plain, (![A_447]: (m1_connsp_2(A_447, '#skF_2', '#skF_3') | ~m1_subset_1(A_447, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_9175])).
% 16.96/8.32  tff(c_12840, plain, (![A_563]: (m1_connsp_2(A_563, '#skF_2', '#skF_3') | ~m1_subset_1(A_563, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_563) | ~r1_tarski(A_563, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_9180])).
% 16.96/8.32  tff(c_12874, plain, (![A_15]: (m1_connsp_2(A_15, '#skF_2', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), A_15) | ~r1_tarski(A_15, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_12840])).
% 16.96/8.32  tff(c_14311, plain, (![C_622, B_623]: (m1_connsp_2(k2_xboole_0(C_622, B_623), '#skF_2', '#skF_3') | ~r1_tarski(k2_xboole_0(C_622, B_623), u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), k1_tops_1('#skF_2', '#skF_5')) | ~r1_tarski('#skF_5', B_623))), inference(resolution, [status(thm)], [c_14287, c_12874])).
% 16.96/8.32  tff(c_14570, plain, (![C_624, B_625]: (m1_connsp_2(k2_xboole_0(C_624, B_625), '#skF_2', '#skF_3') | ~r1_tarski(k2_xboole_0(C_624, B_625), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_5', B_625))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14311])).
% 16.96/8.32  tff(c_42522, plain, (![A_1202, C_1203]: (m1_connsp_2(k2_xboole_0(A_1202, C_1203), '#skF_2', '#skF_3') | ~r1_tarski('#skF_5', C_1203) | ~r1_tarski(C_1203, u1_struct_0('#skF_2')) | ~r1_tarski(A_1202, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_14570])).
% 16.96/8.32  tff(c_129, plain, (![A_84, B_85, C_86]: (k4_subset_1(A_84, B_85, C_86)=k2_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 16.96/8.32  tff(c_222, plain, (![B_94]: (k4_subset_1(u1_struct_0('#skF_2'), B_94, '#skF_5')=k2_xboole_0(B_94, '#skF_5') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_129])).
% 16.96/8.32  tff(c_241, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_222])).
% 16.96/8.32  tff(c_32, plain, (~m1_connsp_2(k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.96/8.32  tff(c_243, plain, (~m1_connsp_2(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_32])).
% 16.96/8.32  tff(c_42541, plain, (~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42522, c_243])).
% 16.96/8.32  tff(c_42573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_57, c_70, c_42541])).
% 16.96/8.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.96/8.32  
% 16.96/8.32  Inference rules
% 16.96/8.32  ----------------------
% 16.96/8.32  #Ref     : 0
% 16.96/8.32  #Sup     : 8910
% 16.96/8.32  #Fact    : 0
% 16.96/8.32  #Define  : 0
% 16.96/8.32  #Split   : 28
% 16.96/8.32  #Chain   : 0
% 16.96/8.32  #Close   : 0
% 16.96/8.32  
% 16.96/8.32  Ordering : KBO
% 16.96/8.32  
% 16.96/8.32  Simplification rules
% 16.96/8.32  ----------------------
% 16.96/8.32  #Subsume      : 3302
% 16.96/8.32  #Demod        : 5865
% 16.96/8.32  #Tautology    : 3013
% 16.96/8.32  #SimpNegUnit  : 278
% 16.96/8.32  #BackRed      : 43
% 16.96/8.32  
% 16.96/8.32  #Partial instantiations: 0
% 16.96/8.32  #Strategies tried      : 1
% 16.96/8.32  
% 16.96/8.32  Timing (in seconds)
% 16.96/8.32  ----------------------
% 16.96/8.32  Preprocessing        : 0.33
% 16.96/8.32  Parsing              : 0.18
% 16.96/8.32  CNF conversion       : 0.02
% 16.96/8.32  Main loop            : 7.18
% 16.96/8.32  Inferencing          : 1.54
% 16.96/8.32  Reduction            : 2.60
% 16.96/8.32  Demodulation         : 1.92
% 16.96/8.32  BG Simplification    : 0.11
% 16.96/8.32  Subsumption          : 2.56
% 16.96/8.32  Abstraction          : 0.22
% 16.96/8.32  MUC search           : 0.00
% 16.96/8.32  Cooper               : 0.00
% 16.96/8.32  Total                : 7.54
% 16.96/8.32  Index Insertion      : 0.00
% 16.96/8.32  Index Deletion       : 0.00
% 16.96/8.32  Index Matching       : 0.00
% 16.96/8.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
