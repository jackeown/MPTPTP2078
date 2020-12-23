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
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 305 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 (1287 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
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

tff(f_84,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_49,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_51,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_50,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_67,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [D_45] :
      ( ~ r2_hidden('#skF_3',D_45)
      | ~ r1_tarski(D_45,'#skF_4')
      | ~ v3_pre_topc(D_45,'#skF_2')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_213,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_344,plain,(
    ! [B_97,A_98,C_99] :
      ( r1_tarski(B_97,k1_tops_1(A_98,C_99))
      | ~ r1_tarski(B_97,C_99)
      | ~ v3_pre_topc(B_97,A_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_350,plain,(
    ! [B_97] :
      ( r1_tarski(B_97,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_97,'#skF_4')
      | ~ v3_pre_topc(B_97,'#skF_2')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_344])).

tff(c_391,plain,(
    ! [B_106] :
      ( r1_tarski(B_106,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_106,'#skF_4')
      | ~ v3_pre_topc(B_106,'#skF_2')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_350])).

tff(c_398,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_391])).

tff(c_407,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_51,c_398])).

tff(c_60,plain,(
    ! [C_51,B_52,A_53] :
      ( r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [B_54] :
      ( r2_hidden('#skF_3',B_54)
      | ~ r1_tarski('#skF_5',B_54) ) ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_2,B_54] :
      ( r2_hidden('#skF_3',B_2)
      | ~ r1_tarski(B_54,B_2)
      | ~ r1_tarski('#skF_5',B_54) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_419,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_407,c_71])).

tff(c_426,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_419])).

tff(c_443,plain,(
    ! [C_108,A_109,B_110] :
      ( m1_connsp_2(C_108,A_109,B_110)
      | ~ r2_hidden(B_110,k1_tops_1(A_109,C_108))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_445,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_426,c_443])).

tff(c_466,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_20,c_445])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_213,c_466])).

tff(c_504,plain,(
    ! [D_117] :
      ( ~ r2_hidden('#skF_3',D_117)
      | ~ r1_tarski(D_117,'#skF_4')
      | ~ v3_pre_topc(D_117,'#skF_2')
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_511,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_504])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_51,c_50,c_511])).

tff(c_522,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_938,plain,(
    ! [B_190,A_191,C_192] :
      ( r2_hidden(B_190,k1_tops_1(A_191,C_192))
      | ~ m1_connsp_2(C_192,A_191,B_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_subset_1(B_190,u1_struct_0(A_191))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_942,plain,(
    ! [B_190] :
      ( r2_hidden(B_190,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_190)
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_938])).

tff(c_946,plain,(
    ! [B_190] :
      ( r2_hidden(B_190,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_190)
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_942])).

tff(c_977,plain,(
    ! [B_196] :
      ( r2_hidden(B_196,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_196)
      | ~ m1_subset_1(B_196,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_946])).

tff(c_576,plain,(
    ! [A_129,B_130] :
      ( v3_pre_topc(k1_tops_1(A_129,B_130),A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_578,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_576])).

tff(c_581,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_578])).

tff(c_524,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k1_tops_1(A_118,B_119),B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_526,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_524])).

tff(c_529,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_526])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_677,plain,(
    ! [D_150] :
      ( ~ r2_hidden('#skF_3',D_150)
      | ~ r1_tarski(D_150,'#skF_4')
      | ~ v3_pre_topc(D_150,'#skF_2')
      | ~ m1_subset_1(D_150,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_30])).

tff(c_681,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_677])).

tff(c_745,plain,(
    ! [B_167] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_167))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_167),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_167),'#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_681])).

tff(c_752,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_745])).

tff(c_758,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_529,c_752])).

tff(c_982,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_977,c_758])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_522,c_982])).

tff(c_997,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1303,plain,(
    ! [B_259,A_260,C_261] :
      ( r2_hidden(B_259,k1_tops_1(A_260,C_261))
      | ~ m1_connsp_2(C_261,A_260,B_259)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ m1_subset_1(B_259,u1_struct_0(A_260))
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1307,plain,(
    ! [B_259] :
      ( r2_hidden(B_259,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_259)
      | ~ m1_subset_1(B_259,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_1303])).

tff(c_1311,plain,(
    ! [B_259] :
      ( r2_hidden(B_259,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_259)
      | ~ m1_subset_1(B_259,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1307])).

tff(c_1313,plain,(
    ! [B_262] :
      ( r2_hidden(B_262,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_262)
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1311])).

tff(c_1043,plain,(
    ! [A_213,B_214] :
      ( v3_pre_topc(k1_tops_1(A_213,B_214),A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1045,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1043])).

tff(c_1048,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1045])).

tff(c_1019,plain,(
    ! [A_206,B_207] :
      ( r1_tarski(k1_tops_1(A_206,B_207),B_207)
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_pre_topc(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1021,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1019])).

tff(c_1024,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1021])).

tff(c_998,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_45] :
      ( ~ r2_hidden('#skF_3',D_45)
      | ~ r1_tarski(D_45,'#skF_4')
      | ~ v3_pre_topc(D_45,'#skF_2')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1081,plain,(
    ! [D_224] :
      ( ~ r2_hidden('#skF_3',D_224)
      | ~ r1_tarski(D_224,'#skF_4')
      | ~ v3_pre_topc(D_224,'#skF_2')
      | ~ m1_subset_1(D_224,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_998,c_38])).

tff(c_1085,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1081])).

tff(c_1221,plain,(
    ! [B_250] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_250))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_250),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_250),'#skF_2')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1085])).

tff(c_1228,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1221])).

tff(c_1234,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1024,c_1228])).

tff(c_1316,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1313,c_1234])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_997,c_1316])).

tff(c_1327,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1610,plain,(
    ! [B_324,A_325,C_326] :
      ( r2_hidden(B_324,k1_tops_1(A_325,C_326))
      | ~ m1_connsp_2(C_326,A_325,B_324)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_subset_1(B_324,u1_struct_0(A_325))
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1614,plain,(
    ! [B_324] :
      ( r2_hidden(B_324,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_324)
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_1610])).

tff(c_1618,plain,(
    ! [B_324] :
      ( r2_hidden(B_324,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_324)
      | ~ m1_subset_1(B_324,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1614])).

tff(c_1620,plain,(
    ! [B_327] :
      ( r2_hidden(B_327,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_327)
      | ~ m1_subset_1(B_327,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1618])).

tff(c_1378,plain,(
    ! [A_279,B_280] :
      ( v3_pre_topc(k1_tops_1(A_279,B_280),A_279)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0(A_279)))
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1382,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1378])).

tff(c_1386,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1382])).

tff(c_1343,plain,(
    ! [A_271,B_272] :
      ( r1_tarski(k1_tops_1(A_271,B_272),B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1345,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1343])).

tff(c_1348,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1345])).

tff(c_1328,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,(
    ! [D_45] :
      ( ~ r2_hidden('#skF_3',D_45)
      | ~ r1_tarski(D_45,'#skF_4')
      | ~ v3_pre_topc(D_45,'#skF_2')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1363,plain,(
    ! [D_278] :
      ( ~ r2_hidden('#skF_3',D_278)
      | ~ r1_tarski(D_278,'#skF_4')
      | ~ v3_pre_topc(D_278,'#skF_2')
      | ~ m1_subset_1(D_278,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1328,c_34])).

tff(c_1367,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1363])).

tff(c_1476,plain,(
    ! [B_304] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_304))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_304),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_304),'#skF_2')
      | ~ m1_subset_1(B_304,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1367])).

tff(c_1483,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1476])).

tff(c_1489,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1348,c_1483])).

tff(c_1625,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1620,c_1489])).

tff(c_1639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1327,c_1625])).

tff(c_1640,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1897,plain,(
    ! [B_384,A_385,C_386] :
      ( r2_hidden(B_384,k1_tops_1(A_385,C_386))
      | ~ m1_connsp_2(C_386,A_385,B_384)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ m1_subset_1(B_384,u1_struct_0(A_385))
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1901,plain,(
    ! [B_384] :
      ( r2_hidden(B_384,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_384)
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_1897])).

tff(c_1905,plain,(
    ! [B_384] :
      ( r2_hidden(B_384,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_384)
      | ~ m1_subset_1(B_384,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1901])).

tff(c_1907,plain,(
    ! [B_387] :
      ( r2_hidden(B_387,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_387)
      | ~ m1_subset_1(B_387,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1905])).

tff(c_1672,plain,(
    ! [A_341,B_342] :
      ( v3_pre_topc(k1_tops_1(A_341,B_342),A_341)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1674,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1672])).

tff(c_1677,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_1674])).

tff(c_1666,plain,(
    ! [A_339,B_340] :
      ( r1_tarski(k1_tops_1(A_339,B_340),B_340)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ l1_pre_topc(A_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1668,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1666])).

tff(c_1671,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1668])).

tff(c_1641,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_45] :
      ( ~ r2_hidden('#skF_3',D_45)
      | ~ r1_tarski(D_45,'#skF_4')
      | ~ v3_pre_topc(D_45,'#skF_2')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1693,plain,(
    ! [D_349] :
      ( ~ r2_hidden('#skF_3',D_349)
      | ~ r1_tarski(D_349,'#skF_4')
      | ~ v3_pre_topc(D_349,'#skF_2')
      | ~ m1_subset_1(D_349,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1641,c_42])).

tff(c_1697,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1693])).

tff(c_1821,plain,(
    ! [B_375] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_375))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_375),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_375),'#skF_2')
      | ~ m1_subset_1(B_375,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1697])).

tff(c_1828,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1821])).

tff(c_1834,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1677,c_1671,c_1828])).

tff(c_1910,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1907,c_1834])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1640,c_1910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:42 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.82  
% 4.76/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.82  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.77/1.82  
% 4.77/1.82  %Foreground sorts:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Background operators:
% 4.77/1.82  
% 4.77/1.82  
% 4.77/1.82  %Foreground operators:
% 4.77/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.77/1.82  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.77/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.77/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.82  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.77/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.77/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.82  
% 4.77/1.86  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.77/1.86  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.77/1.86  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 4.77/1.86  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.77/1.86  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.77/1.86  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.77/1.86  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.77/1.86  tff(c_22, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_49, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 4.77/1.86  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_51, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 4.77/1.86  tff(c_36, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_50, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 4.77/1.86  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_67, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_48])).
% 4.77/1.86  tff(c_28, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_30, plain, (![D_45]: (~r2_hidden('#skF_3', D_45) | ~r1_tarski(D_45, '#skF_4') | ~v3_pre_topc(D_45, '#skF_2') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_213, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 4.77/1.86  tff(c_26, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.86  tff(c_53, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.86  tff(c_58, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_53])).
% 4.77/1.86  tff(c_344, plain, (![B_97, A_98, C_99]: (r1_tarski(B_97, k1_tops_1(A_98, C_99)) | ~r1_tarski(B_97, C_99) | ~v3_pre_topc(B_97, A_98) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.86  tff(c_350, plain, (![B_97]: (r1_tarski(B_97, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_97, '#skF_4') | ~v3_pre_topc(B_97, '#skF_2') | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_344])).
% 4.77/1.86  tff(c_391, plain, (![B_106]: (r1_tarski(B_106, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_106, '#skF_4') | ~v3_pre_topc(B_106, '#skF_2') | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_350])).
% 4.77/1.86  tff(c_398, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_391])).
% 4.77/1.86  tff(c_407, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_51, c_398])).
% 4.77/1.86  tff(c_60, plain, (![C_51, B_52, A_53]: (r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.86  tff(c_68, plain, (![B_54]: (r2_hidden('#skF_3', B_54) | ~r1_tarski('#skF_5', B_54))), inference(resolution, [status(thm)], [c_50, c_60])).
% 4.77/1.86  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.77/1.86  tff(c_71, plain, (![B_2, B_54]: (r2_hidden('#skF_3', B_2) | ~r1_tarski(B_54, B_2) | ~r1_tarski('#skF_5', B_54))), inference(resolution, [status(thm)], [c_68, c_2])).
% 4.77/1.86  tff(c_419, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_407, c_71])).
% 4.77/1.86  tff(c_426, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_419])).
% 4.77/1.86  tff(c_443, plain, (![C_108, A_109, B_110]: (m1_connsp_2(C_108, A_109, B_110) | ~r2_hidden(B_110, k1_tops_1(A_109, C_108)) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.86  tff(c_445, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_426, c_443])).
% 4.77/1.86  tff(c_466, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_20, c_445])).
% 4.77/1.86  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_213, c_466])).
% 4.77/1.86  tff(c_504, plain, (![D_117]: (~r2_hidden('#skF_3', D_117) | ~r1_tarski(D_117, '#skF_4') | ~v3_pre_topc(D_117, '#skF_2') | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_30])).
% 4.77/1.86  tff(c_511, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_67, c_504])).
% 4.77/1.86  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_51, c_50, c_511])).
% 4.77/1.86  tff(c_522, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 4.77/1.86  tff(c_938, plain, (![B_190, A_191, C_192]: (r2_hidden(B_190, k1_tops_1(A_191, C_192)) | ~m1_connsp_2(C_192, A_191, B_190) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(A_191))) | ~m1_subset_1(B_190, u1_struct_0(A_191)) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.86  tff(c_942, plain, (![B_190]: (r2_hidden(B_190, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_190) | ~m1_subset_1(B_190, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_938])).
% 4.77/1.86  tff(c_946, plain, (![B_190]: (r2_hidden(B_190, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_190) | ~m1_subset_1(B_190, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_942])).
% 4.77/1.86  tff(c_977, plain, (![B_196]: (r2_hidden(B_196, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_196) | ~m1_subset_1(B_196, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_28, c_946])).
% 4.77/1.86  tff(c_576, plain, (![A_129, B_130]: (v3_pre_topc(k1_tops_1(A_129, B_130), A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.86  tff(c_578, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_576])).
% 4.77/1.86  tff(c_581, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_578])).
% 4.77/1.86  tff(c_524, plain, (![A_118, B_119]: (r1_tarski(k1_tops_1(A_118, B_119), B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.86  tff(c_526, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_524])).
% 4.77/1.86  tff(c_529, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_526])).
% 4.77/1.86  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.77/1.86  tff(c_677, plain, (![D_150]: (~r2_hidden('#skF_3', D_150) | ~r1_tarski(D_150, '#skF_4') | ~v3_pre_topc(D_150, '#skF_2') | ~m1_subset_1(D_150, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_522, c_30])).
% 4.77/1.86  tff(c_681, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_677])).
% 4.77/1.86  tff(c_745, plain, (![B_167]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_167)) | ~r1_tarski(k1_tops_1('#skF_2', B_167), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_167), '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_681])).
% 4.77/1.86  tff(c_752, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_745])).
% 4.77/1.86  tff(c_758, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_581, c_529, c_752])).
% 4.77/1.86  tff(c_982, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_977, c_758])).
% 4.77/1.86  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_522, c_982])).
% 4.77/1.86  tff(c_997, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.77/1.86  tff(c_1303, plain, (![B_259, A_260, C_261]: (r2_hidden(B_259, k1_tops_1(A_260, C_261)) | ~m1_connsp_2(C_261, A_260, B_259) | ~m1_subset_1(C_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~m1_subset_1(B_259, u1_struct_0(A_260)) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.86  tff(c_1307, plain, (![B_259]: (r2_hidden(B_259, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_259) | ~m1_subset_1(B_259, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1303])).
% 4.77/1.86  tff(c_1311, plain, (![B_259]: (r2_hidden(B_259, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_259) | ~m1_subset_1(B_259, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1307])).
% 4.77/1.86  tff(c_1313, plain, (![B_262]: (r2_hidden(B_262, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_262) | ~m1_subset_1(B_262, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_28, c_1311])).
% 4.77/1.86  tff(c_1043, plain, (![A_213, B_214]: (v3_pre_topc(k1_tops_1(A_213, B_214), A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_213))) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.86  tff(c_1045, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1043])).
% 4.77/1.86  tff(c_1048, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1045])).
% 4.77/1.86  tff(c_1019, plain, (![A_206, B_207]: (r1_tarski(k1_tops_1(A_206, B_207), B_207) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_pre_topc(A_206))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.86  tff(c_1021, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1019])).
% 4.77/1.86  tff(c_1024, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1021])).
% 4.77/1.86  tff(c_998, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.77/1.86  tff(c_38, plain, (![D_45]: (~r2_hidden('#skF_3', D_45) | ~r1_tarski(D_45, '#skF_4') | ~v3_pre_topc(D_45, '#skF_2') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_1081, plain, (![D_224]: (~r2_hidden('#skF_3', D_224) | ~r1_tarski(D_224, '#skF_4') | ~v3_pre_topc(D_224, '#skF_2') | ~m1_subset_1(D_224, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_998, c_38])).
% 4.77/1.86  tff(c_1085, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1081])).
% 4.77/1.86  tff(c_1221, plain, (![B_250]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_250)) | ~r1_tarski(k1_tops_1('#skF_2', B_250), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_250), '#skF_2') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1085])).
% 4.77/1.86  tff(c_1228, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1221])).
% 4.77/1.86  tff(c_1234, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1048, c_1024, c_1228])).
% 4.77/1.86  tff(c_1316, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1313, c_1234])).
% 4.77/1.86  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_997, c_1316])).
% 4.77/1.86  tff(c_1327, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 4.77/1.86  tff(c_1610, plain, (![B_324, A_325, C_326]: (r2_hidden(B_324, k1_tops_1(A_325, C_326)) | ~m1_connsp_2(C_326, A_325, B_324) | ~m1_subset_1(C_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_subset_1(B_324, u1_struct_0(A_325)) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.86  tff(c_1614, plain, (![B_324]: (r2_hidden(B_324, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_324) | ~m1_subset_1(B_324, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1610])).
% 4.77/1.86  tff(c_1618, plain, (![B_324]: (r2_hidden(B_324, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_324) | ~m1_subset_1(B_324, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1614])).
% 4.77/1.86  tff(c_1620, plain, (![B_327]: (r2_hidden(B_327, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_327) | ~m1_subset_1(B_327, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_28, c_1618])).
% 4.77/1.86  tff(c_1378, plain, (![A_279, B_280]: (v3_pre_topc(k1_tops_1(A_279, B_280), A_279) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0(A_279))) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.86  tff(c_1382, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1378])).
% 4.77/1.86  tff(c_1386, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1382])).
% 4.77/1.86  tff(c_1343, plain, (![A_271, B_272]: (r1_tarski(k1_tops_1(A_271, B_272), B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.86  tff(c_1345, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1343])).
% 4.77/1.86  tff(c_1348, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1345])).
% 4.77/1.86  tff(c_1328, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 4.77/1.86  tff(c_34, plain, (![D_45]: (~r2_hidden('#skF_3', D_45) | ~r1_tarski(D_45, '#skF_4') | ~v3_pre_topc(D_45, '#skF_2') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_1363, plain, (![D_278]: (~r2_hidden('#skF_3', D_278) | ~r1_tarski(D_278, '#skF_4') | ~v3_pre_topc(D_278, '#skF_2') | ~m1_subset_1(D_278, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1328, c_34])).
% 4.77/1.86  tff(c_1367, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1363])).
% 4.77/1.86  tff(c_1476, plain, (![B_304]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_304)) | ~r1_tarski(k1_tops_1('#skF_2', B_304), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_304), '#skF_2') | ~m1_subset_1(B_304, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1367])).
% 4.77/1.86  tff(c_1483, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1476])).
% 4.77/1.86  tff(c_1489, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1348, c_1483])).
% 4.77/1.86  tff(c_1625, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1620, c_1489])).
% 4.77/1.86  tff(c_1639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1327, c_1625])).
% 4.77/1.86  tff(c_1640, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.77/1.86  tff(c_1897, plain, (![B_384, A_385, C_386]: (r2_hidden(B_384, k1_tops_1(A_385, C_386)) | ~m1_connsp_2(C_386, A_385, B_384) | ~m1_subset_1(C_386, k1_zfmisc_1(u1_struct_0(A_385))) | ~m1_subset_1(B_384, u1_struct_0(A_385)) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.77/1.86  tff(c_1901, plain, (![B_384]: (r2_hidden(B_384, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_384) | ~m1_subset_1(B_384, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1897])).
% 4.77/1.86  tff(c_1905, plain, (![B_384]: (r2_hidden(B_384, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_384) | ~m1_subset_1(B_384, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1901])).
% 4.77/1.86  tff(c_1907, plain, (![B_387]: (r2_hidden(B_387, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_387) | ~m1_subset_1(B_387, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_28, c_1905])).
% 4.77/1.86  tff(c_1672, plain, (![A_341, B_342]: (v3_pre_topc(k1_tops_1(A_341, B_342), A_341) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.77/1.86  tff(c_1674, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1672])).
% 4.77/1.86  tff(c_1677, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_1674])).
% 4.77/1.86  tff(c_1666, plain, (![A_339, B_340]: (r1_tarski(k1_tops_1(A_339, B_340), B_340) | ~m1_subset_1(B_340, k1_zfmisc_1(u1_struct_0(A_339))) | ~l1_pre_topc(A_339))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.77/1.86  tff(c_1668, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1666])).
% 4.77/1.86  tff(c_1671, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1668])).
% 4.77/1.86  tff(c_1641, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.77/1.86  tff(c_42, plain, (![D_45]: (~r2_hidden('#skF_3', D_45) | ~r1_tarski(D_45, '#skF_4') | ~v3_pre_topc(D_45, '#skF_2') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.77/1.86  tff(c_1693, plain, (![D_349]: (~r2_hidden('#skF_3', D_349) | ~r1_tarski(D_349, '#skF_4') | ~v3_pre_topc(D_349, '#skF_2') | ~m1_subset_1(D_349, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1641, c_42])).
% 4.77/1.86  tff(c_1697, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1693])).
% 4.77/1.86  tff(c_1821, plain, (![B_375]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_375)) | ~r1_tarski(k1_tops_1('#skF_2', B_375), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_375), '#skF_2') | ~m1_subset_1(B_375, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1697])).
% 4.77/1.86  tff(c_1828, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1821])).
% 4.77/1.86  tff(c_1834, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1677, c_1671, c_1828])).
% 4.77/1.86  tff(c_1910, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1907, c_1834])).
% 4.77/1.86  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1640, c_1910])).
% 4.77/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.77/1.86  
% 4.77/1.86  Inference rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Ref     : 0
% 4.77/1.86  #Sup     : 394
% 4.77/1.86  #Fact    : 0
% 4.77/1.86  #Define  : 0
% 4.77/1.86  #Split   : 11
% 4.77/1.86  #Chain   : 0
% 4.77/1.86  #Close   : 0
% 4.77/1.86  
% 4.77/1.86  Ordering : KBO
% 4.77/1.86  
% 4.77/1.86  Simplification rules
% 4.77/1.86  ----------------------
% 4.77/1.86  #Subsume      : 97
% 4.77/1.86  #Demod        : 189
% 4.77/1.86  #Tautology    : 69
% 4.77/1.86  #SimpNegUnit  : 15
% 4.77/1.86  #BackRed      : 0
% 4.77/1.86  
% 4.77/1.86  #Partial instantiations: 0
% 4.77/1.86  #Strategies tried      : 1
% 4.77/1.86  
% 4.77/1.86  Timing (in seconds)
% 4.77/1.86  ----------------------
% 4.77/1.86  Preprocessing        : 0.31
% 4.77/1.86  Parsing              : 0.17
% 4.77/1.86  CNF conversion       : 0.03
% 4.77/1.86  Main loop            : 0.75
% 4.77/1.86  Inferencing          : 0.28
% 4.77/1.86  Reduction            : 0.20
% 4.77/1.86  Demodulation         : 0.14
% 4.77/1.86  BG Simplification    : 0.03
% 4.77/1.86  Subsumption          : 0.20
% 4.77/1.86  Abstraction          : 0.03
% 4.77/1.86  MUC search           : 0.00
% 4.77/1.86  Cooper               : 0.00
% 4.77/1.86  Total                : 1.13
% 4.77/1.86  Index Insertion      : 0.00
% 4.77/1.86  Index Deletion       : 0.00
% 4.77/1.86  Index Matching       : 0.00
% 4.77/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
