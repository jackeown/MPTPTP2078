%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 214 expanded)
%              Number of leaves         :   26 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  199 ( 956 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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

tff(f_90,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_24,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_206,plain,(
    ! [B_79,A_80,C_81] :
      ( r2_hidden(B_79,k1_tops_1(A_80,C_81))
      | ~ m1_connsp_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_subset_1(B_79,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_210,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_206])).

tff(c_214,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_210])).

tff(c_215,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_79)
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_214])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tops_1(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    ! [A_58,B_59] :
      ( v3_pre_topc(k1_tops_1(A_58,B_59),A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_66])).

tff(c_74,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_70])).

tff(c_14,plain,(
    ! [B_20,D_26,C_24,A_12] :
      ( k1_tops_1(B_20,D_26) = D_26
      | ~ v3_pre_topc(D_26,B_20)
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0(B_20)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(B_20)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    ! [C_68,A_69] :
      ( ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_106,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_106])).

tff(c_113,plain,(
    ! [B_70,D_71] :
      ( k1_tops_1(B_70,D_71) = D_71
      | ~ v3_pre_topc(D_71,B_70)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ l1_pre_topc(B_70) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_147,plain,(
    ! [A_77,B_78] :
      ( k1_tops_1(A_77,k1_tops_1(A_77,B_78)) = k1_tops_1(A_77,B_78)
      | ~ v3_pre_topc(k1_tops_1(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_151,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_155,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_151])).

tff(c_222,plain,(
    ! [C_83,A_84,B_85] :
      ( m1_connsp_2(C_83,A_84,B_85)
      | ~ r2_hidden(B_85,k1_tops_1(A_84,C_83))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_226,plain,(
    ! [B_85] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_85)
      | ~ r2_hidden(B_85,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_222])).

tff(c_235,plain,(
    ! [B_85] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_85)
      | ~ r2_hidden(B_85,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_226])).

tff(c_236,plain,(
    ! [B_85] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_85)
      | ~ r2_hidden(B_85,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_235])).

tff(c_238,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_241,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_241])).

tff(c_290,plain,(
    ! [B_86] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_86)
      | ~ r2_hidden(B_86,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_41,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tops_1(A_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_46,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_43])).

tff(c_55,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k1_tops_1(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [D_49] :
      ( ~ r1_tarski(D_49,'#skF_4')
      | ~ v3_pre_topc(D_49,'#skF_2')
      | ~ m1_connsp_2(D_49,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_49,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_59,plain,(
    ! [B_57] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_57),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_57),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_57),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_22])).

tff(c_84,plain,(
    ! [B_67] :
      ( ~ r1_tarski(k1_tops_1('#skF_2',B_67),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_67),'#skF_2')
      | ~ m1_connsp_2(k1_tops_1('#skF_2',B_67),'#skF_2','#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_2',B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_59])).

tff(c_91,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_97,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_46,c_91])).

tff(c_98,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_293,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_290,c_98])).

tff(c_298,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_293])).

tff(c_305,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_215,c_298])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_305])).

tff(c_310,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_494,plain,(
    ! [B_98,A_99,C_100] :
      ( r2_hidden(B_98,k1_tops_1(A_99,C_100))
      | ~ m1_connsp_2(C_100,A_99,B_98)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_98,u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_500,plain,(
    ! [B_98] :
      ( r2_hidden(B_98,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_494])).

tff(c_508,plain,(
    ! [B_98] :
      ( r2_hidden(B_98,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_98)
      | ~ m1_subset_1(B_98,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_500])).

tff(c_510,plain,(
    ! [B_101] :
      ( r2_hidden(B_101,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_101)
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_508])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,(
    ! [B_101] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_101)
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_510,c_2])).

tff(c_517,plain,(
    ! [B_102] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_102)
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_513])).

tff(c_520,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_517])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.50  
% 2.74/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.50  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.74/1.50  
% 2.74/1.50  %Foreground sorts:
% 2.74/1.50  
% 2.74/1.50  
% 2.74/1.50  %Background operators:
% 2.74/1.50  
% 2.74/1.50  
% 2.74/1.50  %Foreground operators:
% 2.74/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.50  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.74/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.50  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.74/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.50  
% 2.90/1.52  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 2.90/1.52  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.90/1.52  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.90/1.52  tff(f_45, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.90/1.52  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 2.90/1.52  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.90/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.90/1.52  tff(c_24, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_206, plain, (![B_79, A_80, C_81]: (r2_hidden(B_79, k1_tops_1(A_80, C_81)) | ~m1_connsp_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_subset_1(B_79, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.52  tff(c_210, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_206])).
% 2.90/1.52  tff(c_214, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_210])).
% 2.90/1.52  tff(c_215, plain, (![B_79]: (r2_hidden(B_79, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_79) | ~m1_subset_1(B_79, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_214])).
% 2.90/1.52  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k1_tops_1(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.52  tff(c_66, plain, (![A_58, B_59]: (v3_pre_topc(k1_tops_1(A_58, B_59), A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.90/1.52  tff(c_70, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_66])).
% 2.90/1.52  tff(c_74, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_70])).
% 2.90/1.52  tff(c_14, plain, (![B_20, D_26, C_24, A_12]: (k1_tops_1(B_20, D_26)=D_26 | ~v3_pre_topc(D_26, B_20) | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0(B_20))) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(B_20) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.90/1.52  tff(c_100, plain, (![C_68, A_69]: (~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(splitLeft, [status(thm)], [c_14])).
% 2.90/1.52  tff(c_106, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_100])).
% 2.90/1.52  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_106])).
% 2.90/1.52  tff(c_113, plain, (![B_70, D_71]: (k1_tops_1(B_70, D_71)=D_71 | ~v3_pre_topc(D_71, B_70) | ~m1_subset_1(D_71, k1_zfmisc_1(u1_struct_0(B_70))) | ~l1_pre_topc(B_70))), inference(splitRight, [status(thm)], [c_14])).
% 2.90/1.52  tff(c_147, plain, (![A_77, B_78]: (k1_tops_1(A_77, k1_tops_1(A_77, B_78))=k1_tops_1(A_77, B_78) | ~v3_pre_topc(k1_tops_1(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_6, c_113])).
% 2.90/1.52  tff(c_151, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_74, c_147])).
% 2.90/1.52  tff(c_155, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_151])).
% 2.90/1.52  tff(c_222, plain, (![C_83, A_84, B_85]: (m1_connsp_2(C_83, A_84, B_85) | ~r2_hidden(B_85, k1_tops_1(A_84, C_83)) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.52  tff(c_226, plain, (![B_85]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_85) | ~r2_hidden(B_85, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_222])).
% 2.90/1.52  tff(c_235, plain, (![B_85]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_85) | ~r2_hidden(B_85, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_226])).
% 2.90/1.52  tff(c_236, plain, (![B_85]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_85) | ~r2_hidden(B_85, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_235])).
% 2.90/1.52  tff(c_238, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_236])).
% 2.90/1.52  tff(c_241, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_238])).
% 2.90/1.52  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_241])).
% 2.90/1.52  tff(c_290, plain, (![B_86]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_86) | ~r2_hidden(B_86, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_86, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_236])).
% 2.90/1.52  tff(c_41, plain, (![A_53, B_54]: (r1_tarski(k1_tops_1(A_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.90/1.52  tff(c_43, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.90/1.52  tff(c_46, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_43])).
% 2.90/1.52  tff(c_55, plain, (![A_56, B_57]: (m1_subset_1(k1_tops_1(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.52  tff(c_22, plain, (![D_49]: (~r1_tarski(D_49, '#skF_4') | ~v3_pre_topc(D_49, '#skF_2') | ~m1_connsp_2(D_49, '#skF_2', '#skF_3') | ~m1_subset_1(D_49, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_49))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.90/1.52  tff(c_59, plain, (![B_57]: (~r1_tarski(k1_tops_1('#skF_2', B_57), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_57), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_57), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_55, c_22])).
% 2.90/1.52  tff(c_84, plain, (![B_67]: (~r1_tarski(k1_tops_1('#skF_2', B_67), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_67), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', B_67), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', B_67)) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_59])).
% 2.90/1.52  tff(c_91, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_84])).
% 2.90/1.52  tff(c_97, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_46, c_91])).
% 2.90/1.52  tff(c_98, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_97])).
% 2.90/1.52  tff(c_293, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_290, c_98])).
% 2.90/1.52  tff(c_298, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_293])).
% 2.90/1.52  tff(c_305, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_215, c_298])).
% 2.90/1.52  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_305])).
% 2.90/1.52  tff(c_310, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_97])).
% 2.90/1.52  tff(c_494, plain, (![B_98, A_99, C_100]: (r2_hidden(B_98, k1_tops_1(A_99, C_100)) | ~m1_connsp_2(C_100, A_99, B_98) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_98, u1_struct_0(A_99)) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.52  tff(c_500, plain, (![B_98]: (r2_hidden(B_98, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_98) | ~m1_subset_1(B_98, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_494])).
% 2.90/1.52  tff(c_508, plain, (![B_98]: (r2_hidden(B_98, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_98) | ~m1_subset_1(B_98, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_500])).
% 2.90/1.52  tff(c_510, plain, (![B_101]: (r2_hidden(B_101, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_101) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_34, c_508])).
% 2.90/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.52  tff(c_513, plain, (![B_101]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_101) | ~m1_subset_1(B_101, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_510, c_2])).
% 2.90/1.52  tff(c_517, plain, (![B_102]: (~m1_connsp_2('#skF_4', '#skF_2', B_102) | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_513])).
% 2.90/1.52  tff(c_520, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_517])).
% 2.90/1.52  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_520])).
% 2.90/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.52  
% 2.90/1.52  Inference rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Ref     : 0
% 2.90/1.52  #Sup     : 86
% 2.90/1.52  #Fact    : 0
% 2.90/1.52  #Define  : 0
% 2.90/1.52  #Split   : 9
% 2.90/1.52  #Chain   : 0
% 2.90/1.52  #Close   : 0
% 2.90/1.52  
% 2.90/1.52  Ordering : KBO
% 2.90/1.52  
% 2.90/1.52  Simplification rules
% 2.90/1.52  ----------------------
% 2.90/1.52  #Subsume      : 27
% 2.90/1.52  #Demod        : 199
% 2.90/1.52  #Tautology    : 33
% 2.90/1.52  #SimpNegUnit  : 14
% 2.90/1.52  #BackRed      : 1
% 2.90/1.52  
% 2.90/1.52  #Partial instantiations: 0
% 2.90/1.52  #Strategies tried      : 1
% 2.90/1.52  
% 2.90/1.52  Timing (in seconds)
% 2.90/1.52  ----------------------
% 2.90/1.52  Preprocessing        : 0.39
% 2.90/1.52  Parsing              : 0.21
% 2.90/1.52  CNF conversion       : 0.03
% 2.90/1.52  Main loop            : 0.33
% 2.90/1.52  Inferencing          : 0.12
% 2.90/1.52  Reduction            : 0.10
% 2.90/1.52  Demodulation         : 0.08
% 2.90/1.52  BG Simplification    : 0.02
% 2.90/1.52  Subsumption          : 0.06
% 2.90/1.52  Abstraction          : 0.01
% 2.90/1.52  MUC search           : 0.00
% 2.90/1.52  Cooper               : 0.00
% 2.90/1.52  Total                : 0.76
% 2.90/1.52  Index Insertion      : 0.00
% 2.90/1.52  Index Deletion       : 0.00
% 2.90/1.52  Index Matching       : 0.00
% 2.90/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
