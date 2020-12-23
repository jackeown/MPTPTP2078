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
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 13.57s
% Output     : CNFRefutation 14.02s
% Verified   : 
% Statistics : Number of formulae       :  315 (1413 expanded)
%              Number of leaves         :   29 ( 503 expanded)
%              Depth                    :   32
%              Number of atoms          : 1112 (6440 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_78,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_95,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_126,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_63,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_64,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_56,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_38,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_3',D_61)
      | ~ r1_tarski(D_61,'#skF_4')
      | ~ v3_pre_topc(D_61,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_319,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k1_tops_1(A_14,B_15),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_233,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_1'(A_103,B_104,C_105),B_104)
      | r1_tarski(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_242,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(B_106,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_233,c_4])).

tff(c_251,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tops_1(A_14,B_15),k1_tops_1(A_14,B_15))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_242])).

tff(c_343,plain,(
    ! [B_135,A_136,C_137] :
      ( r1_tarski(B_135,k1_tops_1(A_136,C_137))
      | ~ r1_tarski(B_135,C_137)
      | ~ v3_pre_topc(B_135,A_136)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_355,plain,(
    ! [B_135] :
      ( r1_tarski(B_135,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_135,'#skF_4')
      | ~ v3_pre_topc(B_135,'#skF_2')
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_343])).

tff(c_365,plain,(
    ! [B_138] :
      ( r1_tarski(B_138,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_138,'#skF_4')
      | ~ v3_pre_topc(B_138,'#skF_2')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_355])).

tff(c_376,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_365])).

tff(c_390,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_376])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [C_66,A_67,B_68] :
      ( r2_hidden(C_66,A_67)
      | ~ r2_hidden(C_66,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_3',A_69)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_62,c_75])).

tff(c_93,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_3',B_70)
      | ~ r1_tarski('#skF_5',B_70) ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_3',A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73))
      | ~ r1_tarski('#skF_5',B_74) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_116,plain,(
    ! [B_13,A_12] :
      ( r2_hidden('#skF_3',B_13)
      | ~ r1_tarski('#skF_5',A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_425,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_3',B_142)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_142) ) ),
    inference(resolution,[status(thm)],[c_390,c_116])).

tff(c_429,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_251,c_425])).

tff(c_436,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_429])).

tff(c_20,plain,(
    ! [C_31,A_25,B_29] :
      ( m1_connsp_2(C_31,A_25,B_29)
      | ~ r2_hidden(B_29,k1_tops_1(A_25,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_441,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_436,c_20])).

tff(c_446,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_441])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_319,c_446])).

tff(c_452,plain,(
    ! [D_143] :
      ( ~ r2_hidden('#skF_3',D_143)
      | ~ r1_tarski(D_143,'#skF_4')
      | ~ v3_pre_topc(D_143,'#skF_2')
      | ~ m1_subset_1(D_143,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_463,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_452])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_62,c_463])).

tff(c_479,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_57,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_529,plain,(
    ! [A_156,B_157] :
      ( v3_pre_topc(k1_tops_1(A_156,B_157),A_156)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_534,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_529])).

tff(c_538,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_534])).

tff(c_693,plain,(
    ! [D_193] :
      ( ~ r2_hidden('#skF_3',D_193)
      | ~ r1_tarski(D_193,'#skF_4')
      | ~ v3_pre_topc(D_193,'#skF_2')
      | ~ m1_subset_1(D_193,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_38])).

tff(c_701,plain,(
    ! [B_15] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_15))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_15),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_15),'#skF_2')
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_693])).

tff(c_751,plain,(
    ! [B_205] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_205))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_205),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_205),'#skF_2')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_701])).

tff(c_766,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_751])).

tff(c_774,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_766])).

tff(c_775,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_555,plain,(
    ! [A_164,B_165] :
      ( m1_subset_1(k1_tops_1(A_164,B_165),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_570,plain,(
    ! [A_164,B_165] :
      ( r1_tarski(k1_tops_1(A_164,B_165),u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_555,c_10])).

tff(c_609,plain,(
    ! [A_181,B_182,C_183] :
      ( r2_hidden('#skF_1'(A_181,B_182,C_183),B_182)
      | r1_tarski(B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(A_181))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_618,plain,(
    ! [B_184,A_185] :
      ( r1_tarski(B_184,B_184)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_185)) ) ),
    inference(resolution,[status(thm)],[c_609,c_4])).

tff(c_625,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tops_1(A_14,B_15),k1_tops_1(A_14,B_15))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_14,c_618])).

tff(c_839,plain,(
    ! [B_220,A_221,C_222] :
      ( r1_tarski(B_220,k1_tops_1(A_221,C_222))
      | ~ r1_tarski(B_220,C_222)
      | ~ v3_pre_topc(B_220,A_221)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_931,plain,(
    ! [B_228,A_229,A_230] :
      ( r1_tarski(B_228,k1_tops_1(A_229,A_230))
      | ~ r1_tarski(B_228,A_230)
      | ~ v3_pre_topc(B_228,A_229)
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229)
      | ~ r1_tarski(A_230,u1_struct_0(A_229)) ) ),
    inference(resolution,[status(thm)],[c_12,c_839])).

tff(c_2186,plain,(
    ! [A_444,B_445,A_446] :
      ( r1_tarski(k1_tops_1(A_444,B_445),k1_tops_1(A_444,A_446))
      | ~ r1_tarski(k1_tops_1(A_444,B_445),A_446)
      | ~ v3_pre_topc(k1_tops_1(A_444,B_445),A_444)
      | ~ r1_tarski(A_446,u1_struct_0(A_444))
      | ~ m1_subset_1(B_445,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ l1_pre_topc(A_444) ) ),
    inference(resolution,[status(thm)],[c_14,c_931])).

tff(c_997,plain,(
    ! [B_245,A_246,C_247] :
      ( r2_hidden(B_245,k1_tops_1(A_246,C_247))
      | ~ m1_connsp_2(C_247,A_246,B_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(B_245,u1_struct_0(A_246))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1007,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_997])).

tff(c_1013,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1007])).

tff(c_1015,plain,(
    ! [B_248] :
      ( r2_hidden(B_248,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_248)
      | ~ m1_subset_1(B_248,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1013])).

tff(c_1037,plain,(
    ! [B_249,A_250] :
      ( r2_hidden(B_249,A_250)
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(A_250))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_249)
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1015,c_2])).

tff(c_1057,plain,(
    ! [B_252,B_253] :
      ( r2_hidden(B_252,B_253)
      | ~ m1_connsp_2('#skF_4','#skF_2',B_252)
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_253) ) ),
    inference(resolution,[status(thm)],[c_12,c_1037])).

tff(c_1062,plain,(
    ! [B_253] :
      ( r2_hidden('#skF_3',B_253)
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_253) ) ),
    inference(resolution,[status(thm)],[c_30,c_1057])).

tff(c_1066,plain,(
    ! [B_253] :
      ( r2_hidden('#skF_3',B_253)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_1062])).

tff(c_2194,plain,(
    ! [A_446] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',A_446))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_446)
      | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
      | ~ r1_tarski(A_446,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2186,c_1066])).

tff(c_2203,plain,(
    ! [A_447] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',A_447))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_538,c_2194])).

tff(c_2208,plain,(
    ! [A_447] :
      ( m1_connsp_2(A_447,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2203,c_20])).

tff(c_2217,plain,(
    ! [A_447] :
      ( m1_connsp_2(A_447,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_447,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_447)
      | ~ r1_tarski(A_447,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_2208])).

tff(c_2222,plain,(
    ! [A_449] :
      ( m1_connsp_2(A_449,'#skF_2','#skF_3')
      | ~ m1_subset_1(A_449,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_449)
      | ~ r1_tarski(A_449,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2217])).

tff(c_2246,plain,(
    ! [A_450] :
      ( m1_connsp_2(A_450,'#skF_2','#skF_3')
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_450)
      | ~ r1_tarski(A_450,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_2222])).

tff(c_2273,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_625,c_2246])).

tff(c_2299,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_2273])).

tff(c_2303,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2299])).

tff(c_2315,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_570,c_2303])).

tff(c_2328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_2315])).

tff(c_2330,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2299])).

tff(c_626,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_618])).

tff(c_2369,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2330,c_626])).

tff(c_2329,plain,(
    m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2299])).

tff(c_24,plain,(
    ! [C_35,A_32,B_33] :
      ( m1_subset_1(C_35,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_connsp_2(C_35,A_32,B_33)
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2373,plain,
    ( m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2329,c_24])).

tff(c_2380,plain,
    ( m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_2373])).

tff(c_2381,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2380])).

tff(c_8,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_830,plain,(
    ! [A_216,B_217,C_218,A_219] :
      ( r2_hidden('#skF_1'(A_216,B_217,C_218),A_219)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_219))
      | r1_tarski(B_217,C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_216))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(resolution,[status(thm)],[c_609,c_2])).

tff(c_1248,plain,(
    ! [A_279,C_278,A_276,A_280,B_277] :
      ( r2_hidden('#skF_1'(A_279,B_277,C_278),A_280)
      | ~ m1_subset_1(A_276,k1_zfmisc_1(A_280))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_276))
      | r1_tarski(B_277,C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(A_279))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_279)) ) ),
    inference(resolution,[status(thm)],[c_830,c_2])).

tff(c_1320,plain,(
    ! [B_293,B_296,C_297,A_294,A_295] :
      ( r2_hidden('#skF_1'(A_294,B_296,C_297),B_293)
      | ~ m1_subset_1(B_296,k1_zfmisc_1(A_295))
      | r1_tarski(B_296,C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(A_294))
      | ~ m1_subset_1(B_296,k1_zfmisc_1(A_294))
      | ~ r1_tarski(A_295,B_293) ) ),
    inference(resolution,[status(thm)],[c_12,c_1248])).

tff(c_1332,plain,(
    ! [B_293,C_297,A_294,A_12,B_13] :
      ( r2_hidden('#skF_1'(A_294,A_12,C_297),B_293)
      | r1_tarski(A_12,C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(A_294))
      | ~ m1_subset_1(A_12,k1_zfmisc_1(A_294))
      | ~ r1_tarski(B_13,B_293)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_1320])).

tff(c_5331,plain,(
    ! [A_563,A_564,C_565] :
      ( r2_hidden('#skF_1'(A_563,A_564,C_565),k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_564,C_565)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | ~ m1_subset_1(A_564,k1_zfmisc_1(A_563))
      | ~ r1_tarski(A_564,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2369,c_1332])).

tff(c_5333,plain,(
    ! [A_563,A_564,C_565] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_563,A_564,C_565))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_563,A_564,C_565),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(A_564,C_565)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | ~ m1_subset_1(A_564,k1_zfmisc_1(A_563))
      | ~ r1_tarski(A_564,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_5331,c_20])).

tff(c_5342,plain,(
    ! [A_563,A_564,C_565] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_563,A_564,C_565))
      | ~ m1_subset_1('#skF_1'(A_563,A_564,C_565),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(A_564,C_565)
      | ~ m1_subset_1(C_565,k1_zfmisc_1(A_563))
      | ~ m1_subset_1(A_564,k1_zfmisc_1(A_563))
      | ~ r1_tarski(A_564,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_5333])).

tff(c_5607,plain,(
    ! [A_580,A_581,C_582] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_580,A_581,C_582))
      | ~ m1_subset_1('#skF_1'(A_580,A_581,C_582),u1_struct_0('#skF_2'))
      | r1_tarski(A_581,C_582)
      | ~ m1_subset_1(C_582,k1_zfmisc_1(A_580))
      | ~ m1_subset_1(A_581,k1_zfmisc_1(A_580))
      | ~ r1_tarski(A_581,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_5342])).

tff(c_8303,plain,(
    ! [B_712,C_713] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_712,C_713))
      | ~ r1_tarski(B_712,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_712,C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_712,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_5607])).

tff(c_26,plain,(
    ! [C_42,B_40,A_36] :
      ( r2_hidden(C_42,B_40)
      | ~ m1_connsp_2(B_40,A_36,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_36))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8318,plain,(
    ! [B_712,C_713] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_712,C_713),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_712,C_713),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_712,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_712,C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_712,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8303,c_26])).

tff(c_8341,plain,(
    ! [B_712,C_713] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_712,C_713),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_712,C_713),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_712,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_712,C_713)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_712,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_8318])).

tff(c_8354,plain,(
    ! [B_723,C_724] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_723,C_724),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_723,C_724),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_723,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_723,C_724)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_723,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_8341])).

tff(c_8360,plain,(
    ! [B_725,C_726] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_725,C_726),'#skF_4')
      | ~ r1_tarski(B_725,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_725,C_726)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_725,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_8354])).

tff(c_8364,plain,(
    ! [B_725] :
      ( ~ r1_tarski(B_725,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_725,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_725,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8360,c_4])).

tff(c_8371,plain,(
    ! [B_727] :
      ( ~ r1_tarski(B_727,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_727,'#skF_4')
      | ~ m1_subset_1(B_727,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8364])).

tff(c_8386,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2381,c_8371])).

tff(c_8414,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_8386])).

tff(c_8416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_775,c_8414])).

tff(c_8418,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_8682,plain,(
    ! [B_767,A_768,C_769] :
      ( r2_hidden(B_767,k1_tops_1(A_768,C_769))
      | ~ m1_connsp_2(C_769,A_768,B_767)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(u1_struct_0(A_768)))
      | ~ m1_subset_1(B_767,u1_struct_0(A_768))
      | ~ l1_pre_topc(A_768)
      | ~ v2_pre_topc(A_768)
      | v2_struct_0(A_768) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_8692,plain,(
    ! [B_767] :
      ( r2_hidden(B_767,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_767)
      | ~ m1_subset_1(B_767,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_8682])).

tff(c_8698,plain,(
    ! [B_767] :
      ( r2_hidden(B_767,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_767)
      | ~ m1_subset_1(B_767,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_8692])).

tff(c_8700,plain,(
    ! [B_770] :
      ( r2_hidden(B_770,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_770)
      | ~ m1_subset_1(B_770,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_8698])).

tff(c_535,plain,(
    ! [A_156,A_12] :
      ( v3_pre_topc(k1_tops_1(A_156,A_12),A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | ~ r1_tarski(A_12,u1_struct_0(A_156)) ) ),
    inference(resolution,[status(thm)],[c_12,c_529])).

tff(c_8456,plain,(
    ! [A_734] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_734))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_734),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',A_734),'#skF_2')
      | ~ r1_tarski(A_734,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_751])).

tff(c_8464,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_535,c_8456])).

tff(c_8473,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_8464])).

tff(c_8706,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8700,c_8473])).

tff(c_8723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_479,c_61,c_8418,c_8706])).

tff(c_8724,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_8768,plain,(
    ! [A_783,B_784] :
      ( v3_pre_topc(k1_tops_1(A_783,B_784),A_783)
      | ~ m1_subset_1(B_784,k1_zfmisc_1(u1_struct_0(A_783)))
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8773,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_8768])).

tff(c_8777,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_8773])).

tff(c_8785,plain,(
    ! [A_788,B_789] :
      ( m1_subset_1(k1_tops_1(A_788,B_789),k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ m1_subset_1(B_789,k1_zfmisc_1(u1_struct_0(A_788)))
      | ~ l1_pre_topc(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8725,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_3',D_61)
      | ~ r1_tarski(D_61,'#skF_4')
      | ~ v3_pre_topc(D_61,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_8742,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_3',D_61)
      | ~ r1_tarski(D_61,'#skF_4')
      | ~ v3_pre_topc(D_61,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8725,c_46])).

tff(c_8794,plain,(
    ! [B_789] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_789))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_789),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_789),'#skF_2')
      | ~ m1_subset_1(B_789,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8785,c_8742])).

tff(c_8917,plain,(
    ! [B_823] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_823))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_823),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_823),'#skF_2')
      | ~ m1_subset_1(B_823,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8794])).

tff(c_8932,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_8917])).

tff(c_8940,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8777,c_8932])).

tff(c_8941,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8940])).

tff(c_9141,plain,(
    ! [B_850,A_851,C_852] :
      ( r2_hidden(B_850,k1_tops_1(A_851,C_852))
      | ~ m1_connsp_2(C_852,A_851,B_850)
      | ~ m1_subset_1(C_852,k1_zfmisc_1(u1_struct_0(A_851)))
      | ~ m1_subset_1(B_850,u1_struct_0(A_851))
      | ~ l1_pre_topc(A_851)
      | ~ v2_pre_topc(A_851)
      | v2_struct_0(A_851) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9151,plain,(
    ! [B_850] :
      ( r2_hidden(B_850,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_850)
      | ~ m1_subset_1(B_850,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_9141])).

tff(c_9157,plain,(
    ! [B_850] :
      ( r2_hidden(B_850,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_850)
      | ~ m1_subset_1(B_850,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_9151])).

tff(c_9159,plain,(
    ! [B_853] :
      ( r2_hidden(B_853,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_853)
      | ~ m1_subset_1(B_853,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_9157])).

tff(c_9291,plain,(
    ! [B_870,A_871] :
      ( r1_tarski(B_870,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(A_871))
      | ~ m1_subset_1(B_870,k1_zfmisc_1(A_871))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_871,B_870,k1_tops_1('#skF_2','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_871,B_870,k1_tops_1('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_9159,c_4])).

tff(c_9296,plain,(
    ! [B_6] :
      ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_6,k1_tops_1('#skF_2','#skF_4')))
      | r1_tarski(B_6,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_9291])).

tff(c_9414,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9296])).

tff(c_9417,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_9414])).

tff(c_9424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_9417])).

tff(c_9426,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_9296])).

tff(c_8858,plain,(
    ! [A_804,B_805,C_806] :
      ( r2_hidden('#skF_1'(A_804,B_805,C_806),B_805)
      | r1_tarski(B_805,C_806)
      | ~ m1_subset_1(C_806,k1_zfmisc_1(A_804))
      | ~ m1_subset_1(B_805,k1_zfmisc_1(A_804)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8865,plain,(
    ! [B_805,A_804] :
      ( r1_tarski(B_805,B_805)
      | ~ m1_subset_1(B_805,k1_zfmisc_1(A_804)) ) ),
    inference(resolution,[status(thm)],[c_8858,c_4])).

tff(c_9488,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9426,c_8865])).

tff(c_9297,plain,(
    ! [A_872,B_873,C_874,A_875] :
      ( r2_hidden('#skF_1'(A_872,B_873,C_874),A_875)
      | ~ m1_subset_1(B_873,k1_zfmisc_1(A_875))
      | r1_tarski(B_873,C_874)
      | ~ m1_subset_1(C_874,k1_zfmisc_1(A_872))
      | ~ m1_subset_1(B_873,k1_zfmisc_1(A_872)) ) ),
    inference(resolution,[status(thm)],[c_8858,c_2])).

tff(c_10969,plain,(
    ! [A_962,B_963,A_965,C_961,A_964] :
      ( r2_hidden('#skF_1'(A_965,B_963,C_961),A_964)
      | ~ m1_subset_1(A_962,k1_zfmisc_1(A_964))
      | ~ m1_subset_1(B_963,k1_zfmisc_1(A_962))
      | r1_tarski(B_963,C_961)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(A_965))
      | ~ m1_subset_1(B_963,k1_zfmisc_1(A_965)) ) ),
    inference(resolution,[status(thm)],[c_9297,c_2])).

tff(c_11173,plain,(
    ! [B_981,A_980,C_979,B_977,A_978] :
      ( r2_hidden('#skF_1'(A_980,B_981,C_979),B_977)
      | ~ m1_subset_1(B_981,k1_zfmisc_1(A_978))
      | r1_tarski(B_981,C_979)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(A_980))
      | ~ m1_subset_1(B_981,k1_zfmisc_1(A_980))
      | ~ r1_tarski(A_978,B_977) ) ),
    inference(resolution,[status(thm)],[c_12,c_10969])).

tff(c_11789,plain,(
    ! [B_1011,C_1012,A_1013,A_1014,B_1010] :
      ( r2_hidden('#skF_1'(A_1013,A_1014,C_1012),B_1011)
      | r1_tarski(A_1014,C_1012)
      | ~ m1_subset_1(C_1012,k1_zfmisc_1(A_1013))
      | ~ m1_subset_1(A_1014,k1_zfmisc_1(A_1013))
      | ~ r1_tarski(B_1010,B_1011)
      | ~ r1_tarski(A_1014,B_1010) ) ),
    inference(resolution,[status(thm)],[c_12,c_11173])).

tff(c_12488,plain,(
    ! [A_1066,A_1067,C_1068] :
      ( r2_hidden('#skF_1'(A_1066,A_1067,C_1068),k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_1067,C_1068)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1(A_1066))
      | ~ m1_subset_1(A_1067,k1_zfmisc_1(A_1066))
      | ~ r1_tarski(A_1067,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_9488,c_11789])).

tff(c_12490,plain,(
    ! [A_1066,A_1067,C_1068] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1066,A_1067,C_1068))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_1066,A_1067,C_1068),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(A_1067,C_1068)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1(A_1066))
      | ~ m1_subset_1(A_1067,k1_zfmisc_1(A_1066))
      | ~ r1_tarski(A_1067,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12488,c_20])).

tff(c_12499,plain,(
    ! [A_1066,A_1067,C_1068] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1066,A_1067,C_1068))
      | ~ m1_subset_1('#skF_1'(A_1066,A_1067,C_1068),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(A_1067,C_1068)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1(A_1066))
      | ~ m1_subset_1(A_1067,k1_zfmisc_1(A_1066))
      | ~ r1_tarski(A_1067,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_12490])).

tff(c_12660,plain,(
    ! [A_1084,A_1085,C_1086] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1084,A_1085,C_1086))
      | ~ m1_subset_1('#skF_1'(A_1084,A_1085,C_1086),u1_struct_0('#skF_2'))
      | r1_tarski(A_1085,C_1086)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(A_1084))
      | ~ m1_subset_1(A_1085,k1_zfmisc_1(A_1084))
      | ~ r1_tarski(A_1085,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_12499])).

tff(c_14660,plain,(
    ! [B_1212,C_1213] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_1212,C_1213))
      | ~ r1_tarski(B_1212,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1212,C_1213)
      | ~ m1_subset_1(C_1213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1212,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_12660])).

tff(c_14673,plain,(
    ! [B_1212,C_1213] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1212,C_1213),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1212,C_1213),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_1212,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1212,C_1213)
      | ~ m1_subset_1(C_1213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1212,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_14660,c_26])).

tff(c_14692,plain,(
    ! [B_1212,C_1213] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1212,C_1213),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1212,C_1213),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_1212,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1212,C_1213)
      | ~ m1_subset_1(C_1213,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1212,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_14673])).

tff(c_14891,plain,(
    ! [B_1224,C_1225] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1224,C_1225),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1224,C_1225),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1224,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1224,C_1225)
      | ~ m1_subset_1(C_1225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1224,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_14692])).

tff(c_14897,plain,(
    ! [B_1226,C_1227] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1226,C_1227),'#skF_4')
      | ~ r1_tarski(B_1226,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1226,C_1227)
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1226,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_14891])).

tff(c_14901,plain,(
    ! [B_1226] :
      ( ~ r1_tarski(B_1226,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1226,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1226,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_14897,c_4])).

tff(c_14908,plain,(
    ! [B_1228] :
      ( ~ r1_tarski(B_1228,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1228,'#skF_4')
      | ~ m1_subset_1(B_1228,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14901])).

tff(c_14923,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9426,c_14908])).

tff(c_14951,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9488,c_14923])).

tff(c_14953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8941,c_14951])).

tff(c_14955,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8940])).

tff(c_15254,plain,(
    ! [B_1274,A_1275,C_1276] :
      ( r2_hidden(B_1274,k1_tops_1(A_1275,C_1276))
      | ~ m1_connsp_2(C_1276,A_1275,B_1274)
      | ~ m1_subset_1(C_1276,k1_zfmisc_1(u1_struct_0(A_1275)))
      | ~ m1_subset_1(B_1274,u1_struct_0(A_1275))
      | ~ l1_pre_topc(A_1275)
      | ~ v2_pre_topc(A_1275)
      | v2_struct_0(A_1275) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_15264,plain,(
    ! [B_1274] :
      ( r2_hidden(B_1274,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1274)
      | ~ m1_subset_1(B_1274,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_15254])).

tff(c_15270,plain,(
    ! [B_1274] :
      ( r2_hidden(B_1274,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1274)
      | ~ m1_subset_1(B_1274,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_15264])).

tff(c_15272,plain,(
    ! [B_1277] :
      ( r2_hidden(B_1277,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1277)
      | ~ m1_subset_1(B_1277,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_15270])).

tff(c_8774,plain,(
    ! [A_783,A_12] :
      ( v3_pre_topc(k1_tops_1(A_783,A_12),A_783)
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | ~ r1_tarski(A_12,u1_struct_0(A_783)) ) ),
    inference(resolution,[status(thm)],[c_12,c_8768])).

tff(c_15149,plain,(
    ! [A_1253] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_1253))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_1253),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',A_1253),'#skF_2')
      | ~ r1_tarski(A_1253,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_8917])).

tff(c_15157,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_8774,c_15149])).

tff(c_15166,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_15157])).

tff(c_15276,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_15272,c_15166])).

tff(c_15291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8724,c_61,c_14955,c_15276])).

tff(c_15292,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_15367,plain,(
    ! [A_1295,B_1296] :
      ( v3_pre_topc(k1_tops_1(A_1295,B_1296),A_1295)
      | ~ m1_subset_1(B_1296,k1_zfmisc_1(u1_struct_0(A_1295)))
      | ~ l1_pre_topc(A_1295)
      | ~ v2_pre_topc(A_1295) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15374,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_15367])).

tff(c_15379,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_15374])).

tff(c_15293,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_3',D_61)
      | ~ r1_tarski(D_61,'#skF_4')
      | ~ v3_pre_topc(D_61,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_15335,plain,(
    ! [D_1289] :
      ( ~ r2_hidden('#skF_3',D_1289)
      | ~ r1_tarski(D_1289,'#skF_4')
      | ~ v3_pre_topc(D_1289,'#skF_2')
      | ~ m1_subset_1(D_1289,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15293,c_50])).

tff(c_15339,plain,(
    ! [B_15] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_15))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_15),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_15),'#skF_2')
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_15335])).

tff(c_15486,plain,(
    ! [B_1328] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_1328))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_1328),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_1328),'#skF_2')
      | ~ m1_subset_1(B_1328,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_15339])).

tff(c_15501,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_15486])).

tff(c_15509,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15379,c_15501])).

tff(c_15510,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15509])).

tff(c_15714,plain,(
    ! [B_1361,A_1362,C_1363] :
      ( r2_hidden(B_1361,k1_tops_1(A_1362,C_1363))
      | ~ m1_connsp_2(C_1363,A_1362,B_1361)
      | ~ m1_subset_1(C_1363,k1_zfmisc_1(u1_struct_0(A_1362)))
      | ~ m1_subset_1(B_1361,u1_struct_0(A_1362))
      | ~ l1_pre_topc(A_1362)
      | ~ v2_pre_topc(A_1362)
      | v2_struct_0(A_1362) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_15724,plain,(
    ! [B_1361] :
      ( r2_hidden(B_1361,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1361)
      | ~ m1_subset_1(B_1361,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_15714])).

tff(c_15730,plain,(
    ! [B_1361] :
      ( r2_hidden(B_1361,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1361)
      | ~ m1_subset_1(B_1361,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_15724])).

tff(c_15732,plain,(
    ! [B_1364] :
      ( r2_hidden(B_1364,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1364)
      | ~ m1_subset_1(B_1364,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_15730])).

tff(c_15768,plain,(
    ! [B_1368,A_1369] :
      ( r1_tarski(B_1368,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(A_1369))
      | ~ m1_subset_1(B_1368,k1_zfmisc_1(A_1369))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1369,B_1368,k1_tops_1('#skF_2','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_1369,B_1368,k1_tops_1('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_15732,c_4])).

tff(c_15773,plain,(
    ! [B_6] :
      ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_6,k1_tops_1('#skF_2','#skF_4')))
      | r1_tarski(B_6,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_15768])).

tff(c_15902,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_15773])).

tff(c_15905,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_15902])).

tff(c_15912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_15905])).

tff(c_15914,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_15773])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15430,plain,(
    ! [A_1311,B_1312,C_1313] :
      ( ~ r2_hidden('#skF_1'(A_1311,B_1312,C_1313),C_1313)
      | r1_tarski(B_1312,C_1313)
      | ~ m1_subset_1(C_1313,k1_zfmisc_1(A_1311))
      | ~ m1_subset_1(B_1312,k1_zfmisc_1(A_1311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15435,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(B_6,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_6,c_15430])).

tff(c_15976,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_15914,c_15435])).

tff(c_15401,plain,(
    ! [A_1305,B_1306,C_1307] :
      ( r2_hidden('#skF_1'(A_1305,B_1306,C_1307),B_1306)
      | r1_tarski(B_1306,C_1307)
      | ~ m1_subset_1(C_1307,k1_zfmisc_1(A_1305))
      | ~ m1_subset_1(B_1306,k1_zfmisc_1(A_1305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_15705,plain,(
    ! [A_1357,B_1358,C_1359,A_1360] :
      ( r2_hidden('#skF_1'(A_1357,B_1358,C_1359),A_1360)
      | ~ m1_subset_1(B_1358,k1_zfmisc_1(A_1360))
      | r1_tarski(B_1358,C_1359)
      | ~ m1_subset_1(C_1359,k1_zfmisc_1(A_1357))
      | ~ m1_subset_1(B_1358,k1_zfmisc_1(A_1357)) ) ),
    inference(resolution,[status(thm)],[c_15401,c_2])).

tff(c_17877,plain,(
    ! [A_1477,A_1478,C_1479,B_1480,A_1481] :
      ( r2_hidden('#skF_1'(A_1477,B_1480,C_1479),A_1481)
      | ~ m1_subset_1(A_1478,k1_zfmisc_1(A_1481))
      | ~ m1_subset_1(B_1480,k1_zfmisc_1(A_1478))
      | r1_tarski(B_1480,C_1479)
      | ~ m1_subset_1(C_1479,k1_zfmisc_1(A_1477))
      | ~ m1_subset_1(B_1480,k1_zfmisc_1(A_1477)) ) ),
    inference(resolution,[status(thm)],[c_15705,c_2])).

tff(c_17977,plain,(
    ! [B_1499,B_1495,C_1496,A_1497,A_1498] :
      ( r2_hidden('#skF_1'(A_1497,B_1499,C_1496),B_1495)
      | ~ m1_subset_1(B_1499,k1_zfmisc_1(A_1498))
      | r1_tarski(B_1499,C_1496)
      | ~ m1_subset_1(C_1496,k1_zfmisc_1(A_1497))
      | ~ m1_subset_1(B_1499,k1_zfmisc_1(A_1497))
      | ~ r1_tarski(A_1498,B_1495) ) ),
    inference(resolution,[status(thm)],[c_12,c_17877])).

tff(c_18390,plain,(
    ! [B_1526,C_1528,A_1527,A_1529,B_1530] :
      ( r2_hidden('#skF_1'(A_1529,A_1527,C_1528),B_1530)
      | r1_tarski(A_1527,C_1528)
      | ~ m1_subset_1(C_1528,k1_zfmisc_1(A_1529))
      | ~ m1_subset_1(A_1527,k1_zfmisc_1(A_1529))
      | ~ r1_tarski(B_1526,B_1530)
      | ~ r1_tarski(A_1527,B_1526) ) ),
    inference(resolution,[status(thm)],[c_12,c_17977])).

tff(c_19020,plain,(
    ! [A_1570,A_1571,C_1572] :
      ( r2_hidden('#skF_1'(A_1570,A_1571,C_1572),k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_1571,C_1572)
      | ~ m1_subset_1(C_1572,k1_zfmisc_1(A_1570))
      | ~ m1_subset_1(A_1571,k1_zfmisc_1(A_1570))
      | ~ r1_tarski(A_1571,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_15976,c_18390])).

tff(c_19022,plain,(
    ! [A_1570,A_1571,C_1572] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1570,A_1571,C_1572))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_1570,A_1571,C_1572),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(A_1571,C_1572)
      | ~ m1_subset_1(C_1572,k1_zfmisc_1(A_1570))
      | ~ m1_subset_1(A_1571,k1_zfmisc_1(A_1570))
      | ~ r1_tarski(A_1571,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_19020,c_20])).

tff(c_19031,plain,(
    ! [A_1570,A_1571,C_1572] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1570,A_1571,C_1572))
      | ~ m1_subset_1('#skF_1'(A_1570,A_1571,C_1572),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(A_1571,C_1572)
      | ~ m1_subset_1(C_1572,k1_zfmisc_1(A_1570))
      | ~ m1_subset_1(A_1571,k1_zfmisc_1(A_1570))
      | ~ r1_tarski(A_1571,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_19022])).

tff(c_19162,plain,(
    ! [A_1590,A_1591,C_1592] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_1590,A_1591,C_1592))
      | ~ m1_subset_1('#skF_1'(A_1590,A_1591,C_1592),u1_struct_0('#skF_2'))
      | r1_tarski(A_1591,C_1592)
      | ~ m1_subset_1(C_1592,k1_zfmisc_1(A_1590))
      | ~ m1_subset_1(A_1591,k1_zfmisc_1(A_1590))
      | ~ r1_tarski(A_1591,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_19031])).

tff(c_21223,plain,(
    ! [B_1704,C_1705] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_1704,C_1705))
      | ~ r1_tarski(B_1704,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1704,C_1705)
      | ~ m1_subset_1(C_1705,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1704,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_19162])).

tff(c_21236,plain,(
    ! [B_1704,C_1705] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1704,C_1705),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1704,C_1705),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_1704,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1704,C_1705)
      | ~ m1_subset_1(C_1705,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1704,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_21223,c_26])).

tff(c_21255,plain,(
    ! [B_1704,C_1705] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1704,C_1705),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1704,C_1705),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_1704,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1704,C_1705)
      | ~ m1_subset_1(C_1705,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1704,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_21236])).

tff(c_22110,plain,(
    ! [B_1739,C_1740] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1739,C_1740),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_1739,C_1740),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_1739,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1739,C_1740)
      | ~ m1_subset_1(C_1740,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1739,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_21255])).

tff(c_22274,plain,(
    ! [B_1745,C_1746] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_1745,C_1746),'#skF_4')
      | ~ r1_tarski(B_1745,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1745,C_1746)
      | ~ m1_subset_1(C_1746,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1745,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_22110])).

tff(c_22278,plain,(
    ! [B_1745] :
      ( ~ r1_tarski(B_1745,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1745,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1745,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_22274,c_4])).

tff(c_22385,plain,(
    ! [B_1751] :
      ( ~ r1_tarski(B_1751,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_1751,'#skF_4')
      | ~ m1_subset_1(B_1751,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22278])).

tff(c_22400,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_15914,c_22385])).

tff(c_22427,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15976,c_22400])).

tff(c_22429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15510,c_22427])).

tff(c_22431,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_15509])).

tff(c_22660,plain,(
    ! [B_1776,A_1777,C_1778] :
      ( r2_hidden(B_1776,k1_tops_1(A_1777,C_1778))
      | ~ m1_connsp_2(C_1778,A_1777,B_1776)
      | ~ m1_subset_1(C_1778,k1_zfmisc_1(u1_struct_0(A_1777)))
      | ~ m1_subset_1(B_1776,u1_struct_0(A_1777))
      | ~ l1_pre_topc(A_1777)
      | ~ v2_pre_topc(A_1777)
      | v2_struct_0(A_1777) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22670,plain,(
    ! [B_1776] :
      ( r2_hidden(B_1776,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1776)
      | ~ m1_subset_1(B_1776,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_22660])).

tff(c_22676,plain,(
    ! [B_1776] :
      ( r2_hidden(B_1776,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1776)
      | ~ m1_subset_1(B_1776,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_22670])).

tff(c_22678,plain,(
    ! [B_1779] :
      ( r2_hidden(B_1779,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_1779)
      | ~ m1_subset_1(B_1779,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_22676])).

tff(c_15376,plain,(
    ! [A_1295,A_12] :
      ( v3_pre_topc(k1_tops_1(A_1295,A_12),A_1295)
      | ~ l1_pre_topc(A_1295)
      | ~ v2_pre_topc(A_1295)
      | ~ r1_tarski(A_12,u1_struct_0(A_1295)) ) ),
    inference(resolution,[status(thm)],[c_12,c_15367])).

tff(c_22443,plain,(
    ! [A_1752] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_1752))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_1752),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',A_1752),'#skF_2')
      | ~ r1_tarski(A_1752,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_15486])).

tff(c_22451,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_15376,c_22443])).

tff(c_22460,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_22451])).

tff(c_22682,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22678,c_22460])).

tff(c_22695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_15292,c_61,c_22431,c_22682])).

tff(c_22696,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_22707,plain,(
    ! [A_1785,B_1786] :
      ( v3_pre_topc(k1_tops_1(A_1785,B_1786),A_1785)
      | ~ m1_subset_1(B_1786,k1_zfmisc_1(u1_struct_0(A_1785)))
      | ~ l1_pre_topc(A_1785)
      | ~ v2_pre_topc(A_1785) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22712,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_22707])).

tff(c_22716,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_22712])).

tff(c_22697,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_61] :
      ( ~ r2_hidden('#skF_3',D_61)
      | ~ r1_tarski(D_61,'#skF_4')
      | ~ v3_pre_topc(D_61,'#skF_2')
      | ~ m1_subset_1(D_61,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28951,plain,(
    ! [D_2250] :
      ( ~ r2_hidden('#skF_3',D_2250)
      | ~ r1_tarski(D_2250,'#skF_4')
      | ~ v3_pre_topc(D_2250,'#skF_2')
      | ~ m1_subset_1(D_2250,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22697,c_42])).

tff(c_28955,plain,(
    ! [B_15] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_15))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_15),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_15),'#skF_2')
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_28951])).

tff(c_29061,plain,(
    ! [B_2273] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_2273))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_2273),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_2273),'#skF_2')
      | ~ m1_subset_1(B_2273,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28955])).

tff(c_29076,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_29061])).

tff(c_29084,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22716,c_29076])).

tff(c_29085,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_29084])).

tff(c_29326,plain,(
    ! [B_2320,A_2321,C_2322] :
      ( r2_hidden(B_2320,k1_tops_1(A_2321,C_2322))
      | ~ m1_connsp_2(C_2322,A_2321,B_2320)
      | ~ m1_subset_1(C_2322,k1_zfmisc_1(u1_struct_0(A_2321)))
      | ~ m1_subset_1(B_2320,u1_struct_0(A_2321))
      | ~ l1_pre_topc(A_2321)
      | ~ v2_pre_topc(A_2321)
      | v2_struct_0(A_2321) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_29336,plain,(
    ! [B_2320] :
      ( r2_hidden(B_2320,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2320)
      | ~ m1_subset_1(B_2320,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_29326])).

tff(c_29342,plain,(
    ! [B_2320] :
      ( r2_hidden(B_2320,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2320)
      | ~ m1_subset_1(B_2320,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_29336])).

tff(c_29344,plain,(
    ! [B_2323] :
      ( r2_hidden(B_2323,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2323)
      | ~ m1_subset_1(B_2323,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_29342])).

tff(c_29446,plain,(
    ! [B_2334,A_2335] :
      ( r1_tarski(B_2334,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(A_2335))
      | ~ m1_subset_1(B_2334,k1_zfmisc_1(A_2335))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_2335,B_2334,k1_tops_1('#skF_2','#skF_4')))
      | ~ m1_subset_1('#skF_1'(A_2335,B_2334,k1_tops_1('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_29344,c_4])).

tff(c_29451,plain,(
    ! [B_6] :
      ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_6,k1_tops_1('#skF_2','#skF_4')))
      | r1_tarski(B_6,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_29446])).

tff(c_29560,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_29451])).

tff(c_29563,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_29560])).

tff(c_29570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_29563])).

tff(c_29572,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_29451])).

tff(c_28982,plain,(
    ! [A_2255,B_2256,C_2257] :
      ( r2_hidden('#skF_1'(A_2255,B_2256,C_2257),B_2256)
      | r1_tarski(B_2256,C_2257)
      | ~ m1_subset_1(C_2257,k1_zfmisc_1(A_2255))
      | ~ m1_subset_1(B_2256,k1_zfmisc_1(A_2255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28989,plain,(
    ! [B_2256,A_2255] :
      ( r1_tarski(B_2256,B_2256)
      | ~ m1_subset_1(B_2256,k1_zfmisc_1(A_2255)) ) ),
    inference(resolution,[status(thm)],[c_28982,c_4])).

tff(c_29635,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_29572,c_28989])).

tff(c_29109,plain,(
    ! [A_2278,B_2279,C_2280,A_2281] :
      ( r2_hidden('#skF_1'(A_2278,B_2279,C_2280),A_2281)
      | ~ m1_subset_1(B_2279,k1_zfmisc_1(A_2281))
      | r1_tarski(B_2279,C_2280)
      | ~ m1_subset_1(C_2280,k1_zfmisc_1(A_2278))
      | ~ m1_subset_1(B_2279,k1_zfmisc_1(A_2278)) ) ),
    inference(resolution,[status(thm)],[c_28982,c_2])).

tff(c_30645,plain,(
    ! [C_2410,A_2409,A_2413,A_2412,B_2411] :
      ( r2_hidden('#skF_1'(A_2409,B_2411,C_2410),A_2412)
      | ~ m1_subset_1(A_2413,k1_zfmisc_1(A_2412))
      | ~ m1_subset_1(B_2411,k1_zfmisc_1(A_2413))
      | r1_tarski(B_2411,C_2410)
      | ~ m1_subset_1(C_2410,k1_zfmisc_1(A_2409))
      | ~ m1_subset_1(B_2411,k1_zfmisc_1(A_2409)) ) ),
    inference(resolution,[status(thm)],[c_29109,c_2])).

tff(c_31707,plain,(
    ! [A_2451,B_2448,C_2450,B_2449,A_2452] :
      ( r2_hidden('#skF_1'(A_2452,B_2449,C_2450),B_2448)
      | ~ m1_subset_1(B_2449,k1_zfmisc_1(A_2451))
      | r1_tarski(B_2449,C_2450)
      | ~ m1_subset_1(C_2450,k1_zfmisc_1(A_2452))
      | ~ m1_subset_1(B_2449,k1_zfmisc_1(A_2452))
      | ~ r1_tarski(A_2451,B_2448) ) ),
    inference(resolution,[status(thm)],[c_12,c_30645])).

tff(c_32009,plain,(
    ! [C_2471,A_2473,B_2475,B_2472,A_2474] :
      ( r2_hidden('#skF_1'(A_2473,A_2474,C_2471),B_2475)
      | r1_tarski(A_2474,C_2471)
      | ~ m1_subset_1(C_2471,k1_zfmisc_1(A_2473))
      | ~ m1_subset_1(A_2474,k1_zfmisc_1(A_2473))
      | ~ r1_tarski(B_2472,B_2475)
      | ~ r1_tarski(A_2474,B_2472) ) ),
    inference(resolution,[status(thm)],[c_12,c_31707])).

tff(c_32782,plain,(
    ! [A_2555,A_2556,C_2557] :
      ( r2_hidden('#skF_1'(A_2555,A_2556,C_2557),k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(A_2556,C_2557)
      | ~ m1_subset_1(C_2557,k1_zfmisc_1(A_2555))
      | ~ m1_subset_1(A_2556,k1_zfmisc_1(A_2555))
      | ~ r1_tarski(A_2556,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_29635,c_32009])).

tff(c_32784,plain,(
    ! [A_2555,A_2556,C_2557] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_2555,A_2556,C_2557))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'(A_2555,A_2556,C_2557),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(A_2556,C_2557)
      | ~ m1_subset_1(C_2557,k1_zfmisc_1(A_2555))
      | ~ m1_subset_1(A_2556,k1_zfmisc_1(A_2555))
      | ~ r1_tarski(A_2556,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32782,c_20])).

tff(c_32793,plain,(
    ! [A_2555,A_2556,C_2557] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_2555,A_2556,C_2557))
      | ~ m1_subset_1('#skF_1'(A_2555,A_2556,C_2557),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(A_2556,C_2557)
      | ~ m1_subset_1(C_2557,k1_zfmisc_1(A_2555))
      | ~ m1_subset_1(A_2556,k1_zfmisc_1(A_2555))
      | ~ r1_tarski(A_2556,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_32784])).

tff(c_32894,plain,(
    ! [A_2576,A_2577,C_2578] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(A_2576,A_2577,C_2578))
      | ~ m1_subset_1('#skF_1'(A_2576,A_2577,C_2578),u1_struct_0('#skF_2'))
      | r1_tarski(A_2577,C_2578)
      | ~ m1_subset_1(C_2578,k1_zfmisc_1(A_2576))
      | ~ m1_subset_1(A_2577,k1_zfmisc_1(A_2576))
      | ~ r1_tarski(A_2577,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32793])).

tff(c_36411,plain,(
    ! [B_2806,C_2807] :
      ( m1_connsp_2('#skF_4','#skF_2','#skF_1'(u1_struct_0('#skF_2'),B_2806,C_2807))
      | ~ r1_tarski(B_2806,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2806,C_2807)
      | ~ m1_subset_1(C_2807,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2806,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_32894])).

tff(c_36426,plain,(
    ! [B_2806,C_2807] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2806,C_2807),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2806,C_2807),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_2806,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2806,C_2807)
      | ~ m1_subset_1(C_2807,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2806,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36411,c_26])).

tff(c_36449,plain,(
    ! [B_2806,C_2807] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2806,C_2807),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2806,C_2807),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(B_2806,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2806,C_2807)
      | ~ m1_subset_1(C_2807,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2806,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_36426])).

tff(c_36455,plain,(
    ! [B_2808,C_2809] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2808,C_2809),'#skF_4')
      | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_2'),B_2808,C_2809),u1_struct_0('#skF_2'))
      | ~ r1_tarski(B_2808,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2808,C_2809)
      | ~ m1_subset_1(C_2809,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2808,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36449])).

tff(c_36461,plain,(
    ! [B_2810,C_2811] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_2'),B_2810,C_2811),'#skF_4')
      | ~ r1_tarski(B_2810,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2810,C_2811)
      | ~ m1_subset_1(C_2811,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2810,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_8,c_36455])).

tff(c_36465,plain,(
    ! [B_2810] :
      ( ~ r1_tarski(B_2810,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2810,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_2810,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36461,c_4])).

tff(c_36472,plain,(
    ! [B_2812] :
      ( ~ r1_tarski(B_2812,k1_tops_1('#skF_2','#skF_4'))
      | r1_tarski(B_2812,'#skF_4')
      | ~ m1_subset_1(B_2812,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36465])).

tff(c_36487,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_29572,c_36472])).

tff(c_36515,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29635,c_36487])).

tff(c_36517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29085,c_36515])).

tff(c_36519,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_29084])).

tff(c_36781,plain,(
    ! [B_2854,A_2855,C_2856] :
      ( r2_hidden(B_2854,k1_tops_1(A_2855,C_2856))
      | ~ m1_connsp_2(C_2856,A_2855,B_2854)
      | ~ m1_subset_1(C_2856,k1_zfmisc_1(u1_struct_0(A_2855)))
      | ~ m1_subset_1(B_2854,u1_struct_0(A_2855))
      | ~ l1_pre_topc(A_2855)
      | ~ v2_pre_topc(A_2855)
      | v2_struct_0(A_2855) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36791,plain,(
    ! [B_2854] :
      ( r2_hidden(B_2854,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2854)
      | ~ m1_subset_1(B_2854,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_36781])).

tff(c_36797,plain,(
    ! [B_2854] :
      ( r2_hidden(B_2854,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2854)
      | ~ m1_subset_1(B_2854,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_36791])).

tff(c_36799,plain,(
    ! [B_2857] :
      ( r2_hidden(B_2857,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_2857)
      | ~ m1_subset_1(B_2857,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36797])).

tff(c_22713,plain,(
    ! [A_1785,A_12] :
      ( v3_pre_topc(k1_tops_1(A_1785,A_12),A_1785)
      | ~ l1_pre_topc(A_1785)
      | ~ v2_pre_topc(A_1785)
      | ~ r1_tarski(A_12,u1_struct_0(A_1785)) ) ),
    inference(resolution,[status(thm)],[c_12,c_22707])).

tff(c_36701,plain,(
    ! [A_2840] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_2840))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_2840),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',A_2840),'#skF_2')
      | ~ r1_tarski(A_2840,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_29061])).

tff(c_36709,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22713,c_36701])).

tff(c_36718,plain,(
    ! [A_12] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_12))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_12),'#skF_4')
      | ~ r1_tarski(A_12,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_36709])).

tff(c_36803,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36799,c_36718])).

tff(c_36818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_22696,c_61,c_36519,c_36803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.57/6.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.74/6.78  
% 13.74/6.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.74/6.79  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 13.74/6.79  
% 13.74/6.79  %Foreground sorts:
% 13.74/6.79  
% 13.74/6.79  
% 13.74/6.79  %Background operators:
% 13.74/6.79  
% 13.74/6.79  
% 13.74/6.79  %Foreground operators:
% 13.74/6.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.74/6.79  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 13.74/6.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.74/6.79  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 13.74/6.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.74/6.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.74/6.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.74/6.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.74/6.79  tff('#skF_5', type, '#skF_5': $i).
% 13.74/6.79  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 13.74/6.79  tff('#skF_2', type, '#skF_2': $i).
% 13.74/6.79  tff('#skF_3', type, '#skF_3': $i).
% 13.74/6.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.74/6.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.74/6.79  tff('#skF_4', type, '#skF_4': $i).
% 13.74/6.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.74/6.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.74/6.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.74/6.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.74/6.79  
% 14.02/6.83  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 14.02/6.83  tff(f_56, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 14.02/6.83  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 14.02/6.83  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 14.02/6.83  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.02/6.83  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 14.02/6.83  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 14.02/6.83  tff(f_64, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 14.02/6.83  tff(f_109, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 14.02/6.83  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 14.02/6.83  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_52, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_63, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 14.02/6.83  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_64, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 14.02/6.83  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_62, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 14.02/6.83  tff(c_56, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_70, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_56])).
% 14.02/6.83  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_38, plain, (![D_61]: (~r2_hidden('#skF_3', D_61) | ~r1_tarski(D_61, '#skF_4') | ~v3_pre_topc(D_61, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_319, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 14.02/6.83  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(k1_tops_1(A_14, B_15), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.02/6.83  tff(c_233, plain, (![A_103, B_104, C_105]: (r2_hidden('#skF_1'(A_103, B_104, C_105), B_104) | r1_tarski(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.83  tff(c_4, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.83  tff(c_242, plain, (![B_106, A_107]: (r1_tarski(B_106, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)))), inference(resolution, [status(thm)], [c_233, c_4])).
% 14.02/6.83  tff(c_251, plain, (![A_14, B_15]: (r1_tarski(k1_tops_1(A_14, B_15), k1_tops_1(A_14, B_15)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_14, c_242])).
% 14.02/6.83  tff(c_343, plain, (![B_135, A_136, C_137]: (r1_tarski(B_135, k1_tops_1(A_136, C_137)) | ~r1_tarski(B_135, C_137) | ~v3_pre_topc(B_135, A_136) | ~m1_subset_1(C_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.02/6.83  tff(c_355, plain, (![B_135]: (r1_tarski(B_135, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_135, '#skF_4') | ~v3_pre_topc(B_135, '#skF_2') | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_343])).
% 14.02/6.83  tff(c_365, plain, (![B_138]: (r1_tarski(B_138, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_138, '#skF_4') | ~v3_pre_topc(B_138, '#skF_2') | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_355])).
% 14.02/6.83  tff(c_376, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_365])).
% 14.02/6.83  tff(c_390, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_376])).
% 14.02/6.83  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.02/6.83  tff(c_75, plain, (![C_66, A_67, B_68]: (r2_hidden(C_66, A_67) | ~r2_hidden(C_66, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.02/6.83  tff(c_79, plain, (![A_69]: (r2_hidden('#skF_3', A_69) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_62, c_75])).
% 14.02/6.83  tff(c_93, plain, (![B_70]: (r2_hidden('#skF_3', B_70) | ~r1_tarski('#skF_5', B_70))), inference(resolution, [status(thm)], [c_12, c_79])).
% 14.02/6.83  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.02/6.83  tff(c_104, plain, (![A_73, B_74]: (r2_hidden('#skF_3', A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)) | ~r1_tarski('#skF_5', B_74))), inference(resolution, [status(thm)], [c_93, c_2])).
% 14.02/6.83  tff(c_116, plain, (![B_13, A_12]: (r2_hidden('#skF_3', B_13) | ~r1_tarski('#skF_5', A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_104])).
% 14.02/6.83  tff(c_425, plain, (![B_142]: (r2_hidden('#skF_3', B_142) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_142))), inference(resolution, [status(thm)], [c_390, c_116])).
% 14.02/6.83  tff(c_429, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_251, c_425])).
% 14.02/6.83  tff(c_436, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_429])).
% 14.02/6.83  tff(c_20, plain, (![C_31, A_25, B_29]: (m1_connsp_2(C_31, A_25, B_29) | ~r2_hidden(B_29, k1_tops_1(A_25, C_31)) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_subset_1(B_29, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_441, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_436, c_20])).
% 14.02/6.83  tff(c_446, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_441])).
% 14.02/6.83  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_319, c_446])).
% 14.02/6.83  tff(c_452, plain, (![D_143]: (~r2_hidden('#skF_3', D_143) | ~r1_tarski(D_143, '#skF_4') | ~v3_pre_topc(D_143, '#skF_2') | ~m1_subset_1(D_143, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_38])).
% 14.02/6.83  tff(c_463, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_452])).
% 14.02/6.83  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_62, c_463])).
% 14.02/6.83  tff(c_479, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 14.02/6.83  tff(c_57, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.02/6.83  tff(c_61, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_57])).
% 14.02/6.83  tff(c_529, plain, (![A_156, B_157]: (v3_pre_topc(k1_tops_1(A_156, B_157), A_156) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.02/6.83  tff(c_534, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_529])).
% 14.02/6.83  tff(c_538, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_534])).
% 14.02/6.83  tff(c_693, plain, (![D_193]: (~r2_hidden('#skF_3', D_193) | ~r1_tarski(D_193, '#skF_4') | ~v3_pre_topc(D_193, '#skF_2') | ~m1_subset_1(D_193, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_38])).
% 14.02/6.83  tff(c_701, plain, (![B_15]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_15)) | ~r1_tarski(k1_tops_1('#skF_2', B_15), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_15), '#skF_2') | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_693])).
% 14.02/6.83  tff(c_751, plain, (![B_205]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_205)) | ~r1_tarski(k1_tops_1('#skF_2', B_205), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_205), '#skF_2') | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_701])).
% 14.02/6.83  tff(c_766, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_751])).
% 14.02/6.83  tff(c_774, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_766])).
% 14.02/6.83  tff(c_775, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_774])).
% 14.02/6.83  tff(c_555, plain, (![A_164, B_165]: (m1_subset_1(k1_tops_1(A_164, B_165), k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.02/6.83  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 14.02/6.83  tff(c_570, plain, (![A_164, B_165]: (r1_tarski(k1_tops_1(A_164, B_165), u1_struct_0(A_164)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_555, c_10])).
% 14.02/6.83  tff(c_609, plain, (![A_181, B_182, C_183]: (r2_hidden('#skF_1'(A_181, B_182, C_183), B_182) | r1_tarski(B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(A_181)) | ~m1_subset_1(B_182, k1_zfmisc_1(A_181)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.83  tff(c_618, plain, (![B_184, A_185]: (r1_tarski(B_184, B_184) | ~m1_subset_1(B_184, k1_zfmisc_1(A_185)))), inference(resolution, [status(thm)], [c_609, c_4])).
% 14.02/6.83  tff(c_625, plain, (![A_14, B_15]: (r1_tarski(k1_tops_1(A_14, B_15), k1_tops_1(A_14, B_15)) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_14, c_618])).
% 14.02/6.83  tff(c_839, plain, (![B_220, A_221, C_222]: (r1_tarski(B_220, k1_tops_1(A_221, C_222)) | ~r1_tarski(B_220, C_222) | ~v3_pre_topc(B_220, A_221) | ~m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.02/6.83  tff(c_931, plain, (![B_228, A_229, A_230]: (r1_tarski(B_228, k1_tops_1(A_229, A_230)) | ~r1_tarski(B_228, A_230) | ~v3_pre_topc(B_228, A_229) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229) | ~r1_tarski(A_230, u1_struct_0(A_229)))), inference(resolution, [status(thm)], [c_12, c_839])).
% 14.02/6.83  tff(c_2186, plain, (![A_444, B_445, A_446]: (r1_tarski(k1_tops_1(A_444, B_445), k1_tops_1(A_444, A_446)) | ~r1_tarski(k1_tops_1(A_444, B_445), A_446) | ~v3_pre_topc(k1_tops_1(A_444, B_445), A_444) | ~r1_tarski(A_446, u1_struct_0(A_444)) | ~m1_subset_1(B_445, k1_zfmisc_1(u1_struct_0(A_444))) | ~l1_pre_topc(A_444))), inference(resolution, [status(thm)], [c_14, c_931])).
% 14.02/6.83  tff(c_997, plain, (![B_245, A_246, C_247]: (r2_hidden(B_245, k1_tops_1(A_246, C_247)) | ~m1_connsp_2(C_247, A_246, B_245) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(B_245, u1_struct_0(A_246)) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_1007, plain, (![B_245]: (r2_hidden(B_245, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_997])).
% 14.02/6.83  tff(c_1013, plain, (![B_245]: (r2_hidden(B_245, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1007])).
% 14.02/6.83  tff(c_1015, plain, (![B_248]: (r2_hidden(B_248, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_248) | ~m1_subset_1(B_248, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_1013])).
% 14.02/6.83  tff(c_1037, plain, (![B_249, A_250]: (r2_hidden(B_249, A_250) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(A_250)) | ~m1_connsp_2('#skF_4', '#skF_2', B_249) | ~m1_subset_1(B_249, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1015, c_2])).
% 14.02/6.83  tff(c_1057, plain, (![B_252, B_253]: (r2_hidden(B_252, B_253) | ~m1_connsp_2('#skF_4', '#skF_2', B_252) | ~m1_subset_1(B_252, u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_253))), inference(resolution, [status(thm)], [c_12, c_1037])).
% 14.02/6.83  tff(c_1062, plain, (![B_253]: (r2_hidden('#skF_3', B_253) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_253))), inference(resolution, [status(thm)], [c_30, c_1057])).
% 14.02/6.83  tff(c_1066, plain, (![B_253]: (r2_hidden('#skF_3', B_253) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_253))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_1062])).
% 14.02/6.83  tff(c_2194, plain, (![A_446]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', A_446)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_446) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~r1_tarski(A_446, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2186, c_1066])).
% 14.02/6.83  tff(c_2203, plain, (![A_447]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', A_447)) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_538, c_2194])).
% 14.02/6.83  tff(c_2208, plain, (![A_447]: (m1_connsp_2(A_447, '#skF_2', '#skF_3') | ~m1_subset_1(A_447, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2203, c_20])).
% 14.02/6.83  tff(c_2217, plain, (![A_447]: (m1_connsp_2(A_447, '#skF_2', '#skF_3') | ~m1_subset_1(A_447, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_447) | ~r1_tarski(A_447, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_2208])).
% 14.02/6.83  tff(c_2222, plain, (![A_449]: (m1_connsp_2(A_449, '#skF_2', '#skF_3') | ~m1_subset_1(A_449, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_449) | ~r1_tarski(A_449, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_2217])).
% 14.02/6.83  tff(c_2246, plain, (![A_450]: (m1_connsp_2(A_450, '#skF_2', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_450) | ~r1_tarski(A_450, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_2222])).
% 14.02/6.83  tff(c_2273, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_625, c_2246])).
% 14.02/6.83  tff(c_2299, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_2273])).
% 14.02/6.83  tff(c_2303, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2299])).
% 14.02/6.83  tff(c_2315, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_570, c_2303])).
% 14.02/6.83  tff(c_2328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_2315])).
% 14.02/6.83  tff(c_2330, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2299])).
% 14.02/6.83  tff(c_626, plain, (![A_12, B_13]: (r1_tarski(A_12, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_618])).
% 14.02/6.83  tff(c_2369, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_2330, c_626])).
% 14.02/6.83  tff(c_2329, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_2299])).
% 14.02/6.83  tff(c_24, plain, (![C_35, A_32, B_33]: (m1_subset_1(C_35, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_connsp_2(C_35, A_32, B_33) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.02/6.83  tff(c_2373, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2329, c_24])).
% 14.02/6.83  tff(c_2380, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_2373])).
% 14.02/6.83  tff(c_2381, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_2380])).
% 14.02/6.83  tff(c_8, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.83  tff(c_830, plain, (![A_216, B_217, C_218, A_219]: (r2_hidden('#skF_1'(A_216, B_217, C_218), A_219) | ~m1_subset_1(B_217, k1_zfmisc_1(A_219)) | r1_tarski(B_217, C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(A_216)) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(resolution, [status(thm)], [c_609, c_2])).
% 14.02/6.83  tff(c_1248, plain, (![A_279, C_278, A_276, A_280, B_277]: (r2_hidden('#skF_1'(A_279, B_277, C_278), A_280) | ~m1_subset_1(A_276, k1_zfmisc_1(A_280)) | ~m1_subset_1(B_277, k1_zfmisc_1(A_276)) | r1_tarski(B_277, C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(A_279)) | ~m1_subset_1(B_277, k1_zfmisc_1(A_279)))), inference(resolution, [status(thm)], [c_830, c_2])).
% 14.02/6.83  tff(c_1320, plain, (![B_293, B_296, C_297, A_294, A_295]: (r2_hidden('#skF_1'(A_294, B_296, C_297), B_293) | ~m1_subset_1(B_296, k1_zfmisc_1(A_295)) | r1_tarski(B_296, C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(A_294)) | ~m1_subset_1(B_296, k1_zfmisc_1(A_294)) | ~r1_tarski(A_295, B_293))), inference(resolution, [status(thm)], [c_12, c_1248])).
% 14.02/6.83  tff(c_1332, plain, (![B_293, C_297, A_294, A_12, B_13]: (r2_hidden('#skF_1'(A_294, A_12, C_297), B_293) | r1_tarski(A_12, C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(A_294)) | ~m1_subset_1(A_12, k1_zfmisc_1(A_294)) | ~r1_tarski(B_13, B_293) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_1320])).
% 14.02/6.83  tff(c_5331, plain, (![A_563, A_564, C_565]: (r2_hidden('#skF_1'(A_563, A_564, C_565), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_564, C_565) | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | ~m1_subset_1(A_564, k1_zfmisc_1(A_563)) | ~r1_tarski(A_564, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_2369, c_1332])).
% 14.02/6.83  tff(c_5333, plain, (![A_563, A_564, C_565]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_563, A_564, C_565)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'(A_563, A_564, C_565), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(A_564, C_565) | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | ~m1_subset_1(A_564, k1_zfmisc_1(A_563)) | ~r1_tarski(A_564, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_5331, c_20])).
% 14.02/6.83  tff(c_5342, plain, (![A_563, A_564, C_565]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_563, A_564, C_565)) | ~m1_subset_1('#skF_1'(A_563, A_564, C_565), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(A_564, C_565) | ~m1_subset_1(C_565, k1_zfmisc_1(A_563)) | ~m1_subset_1(A_564, k1_zfmisc_1(A_563)) | ~r1_tarski(A_564, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_5333])).
% 14.02/6.83  tff(c_5607, plain, (![A_580, A_581, C_582]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_580, A_581, C_582)) | ~m1_subset_1('#skF_1'(A_580, A_581, C_582), u1_struct_0('#skF_2')) | r1_tarski(A_581, C_582) | ~m1_subset_1(C_582, k1_zfmisc_1(A_580)) | ~m1_subset_1(A_581, k1_zfmisc_1(A_580)) | ~r1_tarski(A_581, k1_tops_1('#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_36, c_5342])).
% 14.02/6.83  tff(c_8303, plain, (![B_712, C_713]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_712, C_713)) | ~r1_tarski(B_712, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_712, C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_712, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_5607])).
% 14.02/6.83  tff(c_26, plain, (![C_42, B_40, A_36]: (r2_hidden(C_42, B_40) | ~m1_connsp_2(B_40, A_36, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_36)) | ~m1_subset_1(B_40, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_126])).
% 14.02/6.83  tff(c_8318, plain, (![B_712, C_713]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_712, C_713), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_712, C_713), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_712, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_712, C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_712, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8303, c_26])).
% 14.02/6.83  tff(c_8341, plain, (![B_712, C_713]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_712, C_713), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_712, C_713), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_712, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_712, C_713) | ~m1_subset_1(C_713, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_712, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_8318])).
% 14.02/6.83  tff(c_8354, plain, (![B_723, C_724]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_723, C_724), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_723, C_724), u1_struct_0('#skF_2')) | ~r1_tarski(B_723, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_723, C_724) | ~m1_subset_1(C_724, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_723, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_8341])).
% 14.02/6.83  tff(c_8360, plain, (![B_725, C_726]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_725, C_726), '#skF_4') | ~r1_tarski(B_725, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_725, C_726) | ~m1_subset_1(C_726, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_725, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_8354])).
% 14.02/6.83  tff(c_8364, plain, (![B_725]: (~r1_tarski(B_725, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_725, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_725, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8360, c_4])).
% 14.02/6.83  tff(c_8371, plain, (![B_727]: (~r1_tarski(B_727, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_727, '#skF_4') | ~m1_subset_1(B_727, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8364])).
% 14.02/6.83  tff(c_8386, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_2381, c_8371])).
% 14.02/6.83  tff(c_8414, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_8386])).
% 14.02/6.83  tff(c_8416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_775, c_8414])).
% 14.02/6.83  tff(c_8418, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_774])).
% 14.02/6.83  tff(c_8682, plain, (![B_767, A_768, C_769]: (r2_hidden(B_767, k1_tops_1(A_768, C_769)) | ~m1_connsp_2(C_769, A_768, B_767) | ~m1_subset_1(C_769, k1_zfmisc_1(u1_struct_0(A_768))) | ~m1_subset_1(B_767, u1_struct_0(A_768)) | ~l1_pre_topc(A_768) | ~v2_pre_topc(A_768) | v2_struct_0(A_768))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_8692, plain, (![B_767]: (r2_hidden(B_767, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_767) | ~m1_subset_1(B_767, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_8682])).
% 14.02/6.83  tff(c_8698, plain, (![B_767]: (r2_hidden(B_767, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_767) | ~m1_subset_1(B_767, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_8692])).
% 14.02/6.83  tff(c_8700, plain, (![B_770]: (r2_hidden(B_770, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_770) | ~m1_subset_1(B_770, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_8698])).
% 14.02/6.83  tff(c_535, plain, (![A_156, A_12]: (v3_pre_topc(k1_tops_1(A_156, A_12), A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | ~r1_tarski(A_12, u1_struct_0(A_156)))), inference(resolution, [status(thm)], [c_12, c_529])).
% 14.02/6.83  tff(c_8456, plain, (![A_734]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_734)) | ~r1_tarski(k1_tops_1('#skF_2', A_734), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', A_734), '#skF_2') | ~r1_tarski(A_734, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_751])).
% 14.02/6.83  tff(c_8464, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_535, c_8456])).
% 14.02/6.83  tff(c_8473, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_8464])).
% 14.02/6.83  tff(c_8706, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8700, c_8473])).
% 14.02/6.83  tff(c_8723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_479, c_61, c_8418, c_8706])).
% 14.02/6.83  tff(c_8724, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 14.02/6.83  tff(c_8768, plain, (![A_783, B_784]: (v3_pre_topc(k1_tops_1(A_783, B_784), A_783) | ~m1_subset_1(B_784, k1_zfmisc_1(u1_struct_0(A_783))) | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.02/6.83  tff(c_8773, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_8768])).
% 14.02/6.83  tff(c_8777, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_8773])).
% 14.02/6.83  tff(c_8785, plain, (![A_788, B_789]: (m1_subset_1(k1_tops_1(A_788, B_789), k1_zfmisc_1(u1_struct_0(A_788))) | ~m1_subset_1(B_789, k1_zfmisc_1(u1_struct_0(A_788))) | ~l1_pre_topc(A_788))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.02/6.83  tff(c_8725, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 14.02/6.83  tff(c_46, plain, (![D_61]: (~r2_hidden('#skF_3', D_61) | ~r1_tarski(D_61, '#skF_4') | ~v3_pre_topc(D_61, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_8742, plain, (![D_61]: (~r2_hidden('#skF_3', D_61) | ~r1_tarski(D_61, '#skF_4') | ~v3_pre_topc(D_61, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_8725, c_46])).
% 14.02/6.83  tff(c_8794, plain, (![B_789]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_789)) | ~r1_tarski(k1_tops_1('#skF_2', B_789), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_789), '#skF_2') | ~m1_subset_1(B_789, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8785, c_8742])).
% 14.02/6.83  tff(c_8917, plain, (![B_823]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_823)) | ~r1_tarski(k1_tops_1('#skF_2', B_823), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_823), '#skF_2') | ~m1_subset_1(B_823, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8794])).
% 14.02/6.83  tff(c_8932, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_8917])).
% 14.02/6.83  tff(c_8940, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8777, c_8932])).
% 14.02/6.83  tff(c_8941, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_8940])).
% 14.02/6.83  tff(c_9141, plain, (![B_850, A_851, C_852]: (r2_hidden(B_850, k1_tops_1(A_851, C_852)) | ~m1_connsp_2(C_852, A_851, B_850) | ~m1_subset_1(C_852, k1_zfmisc_1(u1_struct_0(A_851))) | ~m1_subset_1(B_850, u1_struct_0(A_851)) | ~l1_pre_topc(A_851) | ~v2_pre_topc(A_851) | v2_struct_0(A_851))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_9151, plain, (![B_850]: (r2_hidden(B_850, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_850) | ~m1_subset_1(B_850, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_9141])).
% 14.02/6.83  tff(c_9157, plain, (![B_850]: (r2_hidden(B_850, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_850) | ~m1_subset_1(B_850, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_9151])).
% 14.02/6.83  tff(c_9159, plain, (![B_853]: (r2_hidden(B_853, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_853) | ~m1_subset_1(B_853, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_9157])).
% 14.02/6.83  tff(c_9291, plain, (![B_870, A_871]: (r1_tarski(B_870, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(A_871)) | ~m1_subset_1(B_870, k1_zfmisc_1(A_871)) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_871, B_870, k1_tops_1('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_871, B_870, k1_tops_1('#skF_2', '#skF_4')), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_9159, c_4])).
% 14.02/6.83  tff(c_9296, plain, (![B_6]: (~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_6, k1_tops_1('#skF_2', '#skF_4'))) | r1_tarski(B_6, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_9291])).
% 14.02/6.83  tff(c_9414, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_9296])).
% 14.02/6.83  tff(c_9417, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_9414])).
% 14.02/6.83  tff(c_9424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_9417])).
% 14.02/6.83  tff(c_9426, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_9296])).
% 14.02/6.83  tff(c_8858, plain, (![A_804, B_805, C_806]: (r2_hidden('#skF_1'(A_804, B_805, C_806), B_805) | r1_tarski(B_805, C_806) | ~m1_subset_1(C_806, k1_zfmisc_1(A_804)) | ~m1_subset_1(B_805, k1_zfmisc_1(A_804)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.83  tff(c_8865, plain, (![B_805, A_804]: (r1_tarski(B_805, B_805) | ~m1_subset_1(B_805, k1_zfmisc_1(A_804)))), inference(resolution, [status(thm)], [c_8858, c_4])).
% 14.02/6.83  tff(c_9488, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_9426, c_8865])).
% 14.02/6.83  tff(c_9297, plain, (![A_872, B_873, C_874, A_875]: (r2_hidden('#skF_1'(A_872, B_873, C_874), A_875) | ~m1_subset_1(B_873, k1_zfmisc_1(A_875)) | r1_tarski(B_873, C_874) | ~m1_subset_1(C_874, k1_zfmisc_1(A_872)) | ~m1_subset_1(B_873, k1_zfmisc_1(A_872)))), inference(resolution, [status(thm)], [c_8858, c_2])).
% 14.02/6.83  tff(c_10969, plain, (![A_962, B_963, A_965, C_961, A_964]: (r2_hidden('#skF_1'(A_965, B_963, C_961), A_964) | ~m1_subset_1(A_962, k1_zfmisc_1(A_964)) | ~m1_subset_1(B_963, k1_zfmisc_1(A_962)) | r1_tarski(B_963, C_961) | ~m1_subset_1(C_961, k1_zfmisc_1(A_965)) | ~m1_subset_1(B_963, k1_zfmisc_1(A_965)))), inference(resolution, [status(thm)], [c_9297, c_2])).
% 14.02/6.83  tff(c_11173, plain, (![B_981, A_980, C_979, B_977, A_978]: (r2_hidden('#skF_1'(A_980, B_981, C_979), B_977) | ~m1_subset_1(B_981, k1_zfmisc_1(A_978)) | r1_tarski(B_981, C_979) | ~m1_subset_1(C_979, k1_zfmisc_1(A_980)) | ~m1_subset_1(B_981, k1_zfmisc_1(A_980)) | ~r1_tarski(A_978, B_977))), inference(resolution, [status(thm)], [c_12, c_10969])).
% 14.02/6.83  tff(c_11789, plain, (![B_1011, C_1012, A_1013, A_1014, B_1010]: (r2_hidden('#skF_1'(A_1013, A_1014, C_1012), B_1011) | r1_tarski(A_1014, C_1012) | ~m1_subset_1(C_1012, k1_zfmisc_1(A_1013)) | ~m1_subset_1(A_1014, k1_zfmisc_1(A_1013)) | ~r1_tarski(B_1010, B_1011) | ~r1_tarski(A_1014, B_1010))), inference(resolution, [status(thm)], [c_12, c_11173])).
% 14.02/6.83  tff(c_12488, plain, (![A_1066, A_1067, C_1068]: (r2_hidden('#skF_1'(A_1066, A_1067, C_1068), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_1067, C_1068) | ~m1_subset_1(C_1068, k1_zfmisc_1(A_1066)) | ~m1_subset_1(A_1067, k1_zfmisc_1(A_1066)) | ~r1_tarski(A_1067, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_9488, c_11789])).
% 14.02/6.83  tff(c_12490, plain, (![A_1066, A_1067, C_1068]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1066, A_1067, C_1068)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'(A_1066, A_1067, C_1068), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(A_1067, C_1068) | ~m1_subset_1(C_1068, k1_zfmisc_1(A_1066)) | ~m1_subset_1(A_1067, k1_zfmisc_1(A_1066)) | ~r1_tarski(A_1067, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_12488, c_20])).
% 14.02/6.83  tff(c_12499, plain, (![A_1066, A_1067, C_1068]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1066, A_1067, C_1068)) | ~m1_subset_1('#skF_1'(A_1066, A_1067, C_1068), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(A_1067, C_1068) | ~m1_subset_1(C_1068, k1_zfmisc_1(A_1066)) | ~m1_subset_1(A_1067, k1_zfmisc_1(A_1066)) | ~r1_tarski(A_1067, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_12490])).
% 14.02/6.83  tff(c_12660, plain, (![A_1084, A_1085, C_1086]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1084, A_1085, C_1086)) | ~m1_subset_1('#skF_1'(A_1084, A_1085, C_1086), u1_struct_0('#skF_2')) | r1_tarski(A_1085, C_1086) | ~m1_subset_1(C_1086, k1_zfmisc_1(A_1084)) | ~m1_subset_1(A_1085, k1_zfmisc_1(A_1084)) | ~r1_tarski(A_1085, k1_tops_1('#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_36, c_12499])).
% 14.02/6.83  tff(c_14660, plain, (![B_1212, C_1213]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_1212, C_1213)) | ~r1_tarski(B_1212, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1212, C_1213) | ~m1_subset_1(C_1213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1212, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_12660])).
% 14.02/6.83  tff(c_14673, plain, (![B_1212, C_1213]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1212, C_1213), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1212, C_1213), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_1212, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1212, C_1213) | ~m1_subset_1(C_1213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1212, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_14660, c_26])).
% 14.02/6.83  tff(c_14692, plain, (![B_1212, C_1213]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1212, C_1213), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1212, C_1213), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_1212, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1212, C_1213) | ~m1_subset_1(C_1213, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1212, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_14673])).
% 14.02/6.83  tff(c_14891, plain, (![B_1224, C_1225]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1224, C_1225), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1224, C_1225), u1_struct_0('#skF_2')) | ~r1_tarski(B_1224, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1224, C_1225) | ~m1_subset_1(C_1225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1224, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_14692])).
% 14.02/6.83  tff(c_14897, plain, (![B_1226, C_1227]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1226, C_1227), '#skF_4') | ~r1_tarski(B_1226, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1226, C_1227) | ~m1_subset_1(C_1227, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1226, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_14891])).
% 14.02/6.83  tff(c_14901, plain, (![B_1226]: (~r1_tarski(B_1226, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1226, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1226, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_14897, c_4])).
% 14.02/6.83  tff(c_14908, plain, (![B_1228]: (~r1_tarski(B_1228, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1228, '#skF_4') | ~m1_subset_1(B_1228, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14901])).
% 14.02/6.83  tff(c_14923, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9426, c_14908])).
% 14.02/6.83  tff(c_14951, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9488, c_14923])).
% 14.02/6.83  tff(c_14953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8941, c_14951])).
% 14.02/6.83  tff(c_14955, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_8940])).
% 14.02/6.83  tff(c_15254, plain, (![B_1274, A_1275, C_1276]: (r2_hidden(B_1274, k1_tops_1(A_1275, C_1276)) | ~m1_connsp_2(C_1276, A_1275, B_1274) | ~m1_subset_1(C_1276, k1_zfmisc_1(u1_struct_0(A_1275))) | ~m1_subset_1(B_1274, u1_struct_0(A_1275)) | ~l1_pre_topc(A_1275) | ~v2_pre_topc(A_1275) | v2_struct_0(A_1275))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_15264, plain, (![B_1274]: (r2_hidden(B_1274, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1274) | ~m1_subset_1(B_1274, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_15254])).
% 14.02/6.83  tff(c_15270, plain, (![B_1274]: (r2_hidden(B_1274, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1274) | ~m1_subset_1(B_1274, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_15264])).
% 14.02/6.83  tff(c_15272, plain, (![B_1277]: (r2_hidden(B_1277, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1277) | ~m1_subset_1(B_1277, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_15270])).
% 14.02/6.83  tff(c_8774, plain, (![A_783, A_12]: (v3_pre_topc(k1_tops_1(A_783, A_12), A_783) | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | ~r1_tarski(A_12, u1_struct_0(A_783)))), inference(resolution, [status(thm)], [c_12, c_8768])).
% 14.02/6.83  tff(c_15149, plain, (![A_1253]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_1253)) | ~r1_tarski(k1_tops_1('#skF_2', A_1253), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', A_1253), '#skF_2') | ~r1_tarski(A_1253, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_8917])).
% 14.02/6.83  tff(c_15157, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8774, c_15149])).
% 14.02/6.83  tff(c_15166, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_15157])).
% 14.02/6.83  tff(c_15276, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_15272, c_15166])).
% 14.02/6.83  tff(c_15291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_8724, c_61, c_14955, c_15276])).
% 14.02/6.83  tff(c_15292, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 14.02/6.83  tff(c_15367, plain, (![A_1295, B_1296]: (v3_pre_topc(k1_tops_1(A_1295, B_1296), A_1295) | ~m1_subset_1(B_1296, k1_zfmisc_1(u1_struct_0(A_1295))) | ~l1_pre_topc(A_1295) | ~v2_pre_topc(A_1295))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.02/6.83  tff(c_15374, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_15367])).
% 14.02/6.83  tff(c_15379, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_15374])).
% 14.02/6.83  tff(c_15293, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 14.02/6.83  tff(c_50, plain, (![D_61]: (~r2_hidden('#skF_3', D_61) | ~r1_tarski(D_61, '#skF_4') | ~v3_pre_topc(D_61, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.83  tff(c_15335, plain, (![D_1289]: (~r2_hidden('#skF_3', D_1289) | ~r1_tarski(D_1289, '#skF_4') | ~v3_pre_topc(D_1289, '#skF_2') | ~m1_subset_1(D_1289, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_15293, c_50])).
% 14.02/6.83  tff(c_15339, plain, (![B_15]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_15)) | ~r1_tarski(k1_tops_1('#skF_2', B_15), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_15), '#skF_2') | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_15335])).
% 14.02/6.83  tff(c_15486, plain, (![B_1328]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_1328)) | ~r1_tarski(k1_tops_1('#skF_2', B_1328), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_1328), '#skF_2') | ~m1_subset_1(B_1328, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_15339])).
% 14.02/6.83  tff(c_15501, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_15486])).
% 14.02/6.83  tff(c_15509, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15379, c_15501])).
% 14.02/6.83  tff(c_15510, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_15509])).
% 14.02/6.83  tff(c_15714, plain, (![B_1361, A_1362, C_1363]: (r2_hidden(B_1361, k1_tops_1(A_1362, C_1363)) | ~m1_connsp_2(C_1363, A_1362, B_1361) | ~m1_subset_1(C_1363, k1_zfmisc_1(u1_struct_0(A_1362))) | ~m1_subset_1(B_1361, u1_struct_0(A_1362)) | ~l1_pre_topc(A_1362) | ~v2_pre_topc(A_1362) | v2_struct_0(A_1362))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.83  tff(c_15724, plain, (![B_1361]: (r2_hidden(B_1361, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1361) | ~m1_subset_1(B_1361, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_15714])).
% 14.02/6.83  tff(c_15730, plain, (![B_1361]: (r2_hidden(B_1361, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1361) | ~m1_subset_1(B_1361, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_15724])).
% 14.02/6.84  tff(c_15732, plain, (![B_1364]: (r2_hidden(B_1364, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1364) | ~m1_subset_1(B_1364, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_15730])).
% 14.02/6.84  tff(c_15768, plain, (![B_1368, A_1369]: (r1_tarski(B_1368, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(A_1369)) | ~m1_subset_1(B_1368, k1_zfmisc_1(A_1369)) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1369, B_1368, k1_tops_1('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_1369, B_1368, k1_tops_1('#skF_2', '#skF_4')), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_15732, c_4])).
% 14.02/6.84  tff(c_15773, plain, (![B_6]: (~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_6, k1_tops_1('#skF_2', '#skF_4'))) | r1_tarski(B_6, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_15768])).
% 14.02/6.84  tff(c_15902, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_15773])).
% 14.02/6.84  tff(c_15905, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_15902])).
% 14.02/6.84  tff(c_15912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_15905])).
% 14.02/6.84  tff(c_15914, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_15773])).
% 14.02/6.84  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.84  tff(c_15430, plain, (![A_1311, B_1312, C_1313]: (~r2_hidden('#skF_1'(A_1311, B_1312, C_1313), C_1313) | r1_tarski(B_1312, C_1313) | ~m1_subset_1(C_1313, k1_zfmisc_1(A_1311)) | ~m1_subset_1(B_1312, k1_zfmisc_1(A_1311)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.84  tff(c_15435, plain, (![B_6, A_5]: (r1_tarski(B_6, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_6, c_15430])).
% 14.02/6.84  tff(c_15976, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_15914, c_15435])).
% 14.02/6.84  tff(c_15401, plain, (![A_1305, B_1306, C_1307]: (r2_hidden('#skF_1'(A_1305, B_1306, C_1307), B_1306) | r1_tarski(B_1306, C_1307) | ~m1_subset_1(C_1307, k1_zfmisc_1(A_1305)) | ~m1_subset_1(B_1306, k1_zfmisc_1(A_1305)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.84  tff(c_15705, plain, (![A_1357, B_1358, C_1359, A_1360]: (r2_hidden('#skF_1'(A_1357, B_1358, C_1359), A_1360) | ~m1_subset_1(B_1358, k1_zfmisc_1(A_1360)) | r1_tarski(B_1358, C_1359) | ~m1_subset_1(C_1359, k1_zfmisc_1(A_1357)) | ~m1_subset_1(B_1358, k1_zfmisc_1(A_1357)))), inference(resolution, [status(thm)], [c_15401, c_2])).
% 14.02/6.84  tff(c_17877, plain, (![A_1477, A_1478, C_1479, B_1480, A_1481]: (r2_hidden('#skF_1'(A_1477, B_1480, C_1479), A_1481) | ~m1_subset_1(A_1478, k1_zfmisc_1(A_1481)) | ~m1_subset_1(B_1480, k1_zfmisc_1(A_1478)) | r1_tarski(B_1480, C_1479) | ~m1_subset_1(C_1479, k1_zfmisc_1(A_1477)) | ~m1_subset_1(B_1480, k1_zfmisc_1(A_1477)))), inference(resolution, [status(thm)], [c_15705, c_2])).
% 14.02/6.84  tff(c_17977, plain, (![B_1499, B_1495, C_1496, A_1497, A_1498]: (r2_hidden('#skF_1'(A_1497, B_1499, C_1496), B_1495) | ~m1_subset_1(B_1499, k1_zfmisc_1(A_1498)) | r1_tarski(B_1499, C_1496) | ~m1_subset_1(C_1496, k1_zfmisc_1(A_1497)) | ~m1_subset_1(B_1499, k1_zfmisc_1(A_1497)) | ~r1_tarski(A_1498, B_1495))), inference(resolution, [status(thm)], [c_12, c_17877])).
% 14.02/6.84  tff(c_18390, plain, (![B_1526, C_1528, A_1527, A_1529, B_1530]: (r2_hidden('#skF_1'(A_1529, A_1527, C_1528), B_1530) | r1_tarski(A_1527, C_1528) | ~m1_subset_1(C_1528, k1_zfmisc_1(A_1529)) | ~m1_subset_1(A_1527, k1_zfmisc_1(A_1529)) | ~r1_tarski(B_1526, B_1530) | ~r1_tarski(A_1527, B_1526))), inference(resolution, [status(thm)], [c_12, c_17977])).
% 14.02/6.84  tff(c_19020, plain, (![A_1570, A_1571, C_1572]: (r2_hidden('#skF_1'(A_1570, A_1571, C_1572), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_1571, C_1572) | ~m1_subset_1(C_1572, k1_zfmisc_1(A_1570)) | ~m1_subset_1(A_1571, k1_zfmisc_1(A_1570)) | ~r1_tarski(A_1571, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_15976, c_18390])).
% 14.02/6.84  tff(c_19022, plain, (![A_1570, A_1571, C_1572]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1570, A_1571, C_1572)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'(A_1570, A_1571, C_1572), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(A_1571, C_1572) | ~m1_subset_1(C_1572, k1_zfmisc_1(A_1570)) | ~m1_subset_1(A_1571, k1_zfmisc_1(A_1570)) | ~r1_tarski(A_1571, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_19020, c_20])).
% 14.02/6.84  tff(c_19031, plain, (![A_1570, A_1571, C_1572]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1570, A_1571, C_1572)) | ~m1_subset_1('#skF_1'(A_1570, A_1571, C_1572), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(A_1571, C_1572) | ~m1_subset_1(C_1572, k1_zfmisc_1(A_1570)) | ~m1_subset_1(A_1571, k1_zfmisc_1(A_1570)) | ~r1_tarski(A_1571, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_19022])).
% 14.02/6.84  tff(c_19162, plain, (![A_1590, A_1591, C_1592]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_1590, A_1591, C_1592)) | ~m1_subset_1('#skF_1'(A_1590, A_1591, C_1592), u1_struct_0('#skF_2')) | r1_tarski(A_1591, C_1592) | ~m1_subset_1(C_1592, k1_zfmisc_1(A_1590)) | ~m1_subset_1(A_1591, k1_zfmisc_1(A_1590)) | ~r1_tarski(A_1591, k1_tops_1('#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_36, c_19031])).
% 14.02/6.84  tff(c_21223, plain, (![B_1704, C_1705]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_1704, C_1705)) | ~r1_tarski(B_1704, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1704, C_1705) | ~m1_subset_1(C_1705, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1704, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_19162])).
% 14.02/6.84  tff(c_21236, plain, (![B_1704, C_1705]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1704, C_1705), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1704, C_1705), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_1704, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1704, C_1705) | ~m1_subset_1(C_1705, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1704, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_21223, c_26])).
% 14.02/6.84  tff(c_21255, plain, (![B_1704, C_1705]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1704, C_1705), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1704, C_1705), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_1704, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1704, C_1705) | ~m1_subset_1(C_1705, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1704, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_21236])).
% 14.02/6.84  tff(c_22110, plain, (![B_1739, C_1740]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1739, C_1740), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_1739, C_1740), u1_struct_0('#skF_2')) | ~r1_tarski(B_1739, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1739, C_1740) | ~m1_subset_1(C_1740, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1739, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_21255])).
% 14.02/6.84  tff(c_22274, plain, (![B_1745, C_1746]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_1745, C_1746), '#skF_4') | ~r1_tarski(B_1745, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1745, C_1746) | ~m1_subset_1(C_1746, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1745, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_22110])).
% 14.02/6.84  tff(c_22278, plain, (![B_1745]: (~r1_tarski(B_1745, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1745, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1745, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_22274, c_4])).
% 14.02/6.84  tff(c_22385, plain, (![B_1751]: (~r1_tarski(B_1751, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_1751, '#skF_4') | ~m1_subset_1(B_1751, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22278])).
% 14.02/6.84  tff(c_22400, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_15914, c_22385])).
% 14.02/6.84  tff(c_22427, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15976, c_22400])).
% 14.02/6.84  tff(c_22429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15510, c_22427])).
% 14.02/6.84  tff(c_22431, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_15509])).
% 14.02/6.84  tff(c_22660, plain, (![B_1776, A_1777, C_1778]: (r2_hidden(B_1776, k1_tops_1(A_1777, C_1778)) | ~m1_connsp_2(C_1778, A_1777, B_1776) | ~m1_subset_1(C_1778, k1_zfmisc_1(u1_struct_0(A_1777))) | ~m1_subset_1(B_1776, u1_struct_0(A_1777)) | ~l1_pre_topc(A_1777) | ~v2_pre_topc(A_1777) | v2_struct_0(A_1777))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.84  tff(c_22670, plain, (![B_1776]: (r2_hidden(B_1776, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1776) | ~m1_subset_1(B_1776, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_22660])).
% 14.02/6.84  tff(c_22676, plain, (![B_1776]: (r2_hidden(B_1776, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1776) | ~m1_subset_1(B_1776, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_22670])).
% 14.02/6.84  tff(c_22678, plain, (![B_1779]: (r2_hidden(B_1779, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_1779) | ~m1_subset_1(B_1779, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_22676])).
% 14.02/6.84  tff(c_15376, plain, (![A_1295, A_12]: (v3_pre_topc(k1_tops_1(A_1295, A_12), A_1295) | ~l1_pre_topc(A_1295) | ~v2_pre_topc(A_1295) | ~r1_tarski(A_12, u1_struct_0(A_1295)))), inference(resolution, [status(thm)], [c_12, c_15367])).
% 14.02/6.84  tff(c_22443, plain, (![A_1752]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_1752)) | ~r1_tarski(k1_tops_1('#skF_2', A_1752), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', A_1752), '#skF_2') | ~r1_tarski(A_1752, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_15486])).
% 14.02/6.84  tff(c_22451, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_15376, c_22443])).
% 14.02/6.84  tff(c_22460, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_22451])).
% 14.02/6.84  tff(c_22682, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22678, c_22460])).
% 14.02/6.84  tff(c_22695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_15292, c_61, c_22431, c_22682])).
% 14.02/6.84  tff(c_22696, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 14.02/6.84  tff(c_22707, plain, (![A_1785, B_1786]: (v3_pre_topc(k1_tops_1(A_1785, B_1786), A_1785) | ~m1_subset_1(B_1786, k1_zfmisc_1(u1_struct_0(A_1785))) | ~l1_pre_topc(A_1785) | ~v2_pre_topc(A_1785))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.02/6.84  tff(c_22712, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_22707])).
% 14.02/6.84  tff(c_22716, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_22712])).
% 14.02/6.84  tff(c_22697, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 14.02/6.84  tff(c_42, plain, (![D_61]: (~r2_hidden('#skF_3', D_61) | ~r1_tarski(D_61, '#skF_4') | ~v3_pre_topc(D_61, '#skF_2') | ~m1_subset_1(D_61, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.02/6.84  tff(c_28951, plain, (![D_2250]: (~r2_hidden('#skF_3', D_2250) | ~r1_tarski(D_2250, '#skF_4') | ~v3_pre_topc(D_2250, '#skF_2') | ~m1_subset_1(D_2250, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22697, c_42])).
% 14.02/6.84  tff(c_28955, plain, (![B_15]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_15)) | ~r1_tarski(k1_tops_1('#skF_2', B_15), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_15), '#skF_2') | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_28951])).
% 14.02/6.84  tff(c_29061, plain, (![B_2273]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_2273)) | ~r1_tarski(k1_tops_1('#skF_2', B_2273), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_2273), '#skF_2') | ~m1_subset_1(B_2273, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28955])).
% 14.02/6.84  tff(c_29076, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_28, c_29061])).
% 14.02/6.84  tff(c_29084, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22716, c_29076])).
% 14.02/6.84  tff(c_29085, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_29084])).
% 14.02/6.84  tff(c_29326, plain, (![B_2320, A_2321, C_2322]: (r2_hidden(B_2320, k1_tops_1(A_2321, C_2322)) | ~m1_connsp_2(C_2322, A_2321, B_2320) | ~m1_subset_1(C_2322, k1_zfmisc_1(u1_struct_0(A_2321))) | ~m1_subset_1(B_2320, u1_struct_0(A_2321)) | ~l1_pre_topc(A_2321) | ~v2_pre_topc(A_2321) | v2_struct_0(A_2321))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.84  tff(c_29336, plain, (![B_2320]: (r2_hidden(B_2320, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2320) | ~m1_subset_1(B_2320, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_29326])).
% 14.02/6.84  tff(c_29342, plain, (![B_2320]: (r2_hidden(B_2320, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2320) | ~m1_subset_1(B_2320, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_29336])).
% 14.02/6.84  tff(c_29344, plain, (![B_2323]: (r2_hidden(B_2323, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2323) | ~m1_subset_1(B_2323, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_29342])).
% 14.02/6.84  tff(c_29446, plain, (![B_2334, A_2335]: (r1_tarski(B_2334, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(A_2335)) | ~m1_subset_1(B_2334, k1_zfmisc_1(A_2335)) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_2335, B_2334, k1_tops_1('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'(A_2335, B_2334, k1_tops_1('#skF_2', '#skF_4')), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_29344, c_4])).
% 14.02/6.84  tff(c_29451, plain, (![B_6]: (~m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_6, k1_tops_1('#skF_2', '#skF_4'))) | r1_tarski(B_6, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_29446])).
% 14.02/6.84  tff(c_29560, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_29451])).
% 14.02/6.84  tff(c_29563, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_29560])).
% 14.02/6.84  tff(c_29570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_29563])).
% 14.02/6.84  tff(c_29572, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_29451])).
% 14.02/6.84  tff(c_28982, plain, (![A_2255, B_2256, C_2257]: (r2_hidden('#skF_1'(A_2255, B_2256, C_2257), B_2256) | r1_tarski(B_2256, C_2257) | ~m1_subset_1(C_2257, k1_zfmisc_1(A_2255)) | ~m1_subset_1(B_2256, k1_zfmisc_1(A_2255)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.02/6.84  tff(c_28989, plain, (![B_2256, A_2255]: (r1_tarski(B_2256, B_2256) | ~m1_subset_1(B_2256, k1_zfmisc_1(A_2255)))), inference(resolution, [status(thm)], [c_28982, c_4])).
% 14.02/6.84  tff(c_29635, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_29572, c_28989])).
% 14.02/6.84  tff(c_29109, plain, (![A_2278, B_2279, C_2280, A_2281]: (r2_hidden('#skF_1'(A_2278, B_2279, C_2280), A_2281) | ~m1_subset_1(B_2279, k1_zfmisc_1(A_2281)) | r1_tarski(B_2279, C_2280) | ~m1_subset_1(C_2280, k1_zfmisc_1(A_2278)) | ~m1_subset_1(B_2279, k1_zfmisc_1(A_2278)))), inference(resolution, [status(thm)], [c_28982, c_2])).
% 14.02/6.84  tff(c_30645, plain, (![C_2410, A_2409, A_2413, A_2412, B_2411]: (r2_hidden('#skF_1'(A_2409, B_2411, C_2410), A_2412) | ~m1_subset_1(A_2413, k1_zfmisc_1(A_2412)) | ~m1_subset_1(B_2411, k1_zfmisc_1(A_2413)) | r1_tarski(B_2411, C_2410) | ~m1_subset_1(C_2410, k1_zfmisc_1(A_2409)) | ~m1_subset_1(B_2411, k1_zfmisc_1(A_2409)))), inference(resolution, [status(thm)], [c_29109, c_2])).
% 14.02/6.84  tff(c_31707, plain, (![A_2451, B_2448, C_2450, B_2449, A_2452]: (r2_hidden('#skF_1'(A_2452, B_2449, C_2450), B_2448) | ~m1_subset_1(B_2449, k1_zfmisc_1(A_2451)) | r1_tarski(B_2449, C_2450) | ~m1_subset_1(C_2450, k1_zfmisc_1(A_2452)) | ~m1_subset_1(B_2449, k1_zfmisc_1(A_2452)) | ~r1_tarski(A_2451, B_2448))), inference(resolution, [status(thm)], [c_12, c_30645])).
% 14.02/6.84  tff(c_32009, plain, (![C_2471, A_2473, B_2475, B_2472, A_2474]: (r2_hidden('#skF_1'(A_2473, A_2474, C_2471), B_2475) | r1_tarski(A_2474, C_2471) | ~m1_subset_1(C_2471, k1_zfmisc_1(A_2473)) | ~m1_subset_1(A_2474, k1_zfmisc_1(A_2473)) | ~r1_tarski(B_2472, B_2475) | ~r1_tarski(A_2474, B_2472))), inference(resolution, [status(thm)], [c_12, c_31707])).
% 14.02/6.84  tff(c_32782, plain, (![A_2555, A_2556, C_2557]: (r2_hidden('#skF_1'(A_2555, A_2556, C_2557), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(A_2556, C_2557) | ~m1_subset_1(C_2557, k1_zfmisc_1(A_2555)) | ~m1_subset_1(A_2556, k1_zfmisc_1(A_2555)) | ~r1_tarski(A_2556, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_29635, c_32009])).
% 14.02/6.84  tff(c_32784, plain, (![A_2555, A_2556, C_2557]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_2555, A_2556, C_2557)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'(A_2555, A_2556, C_2557), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(A_2556, C_2557) | ~m1_subset_1(C_2557, k1_zfmisc_1(A_2555)) | ~m1_subset_1(A_2556, k1_zfmisc_1(A_2555)) | ~r1_tarski(A_2556, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_32782, c_20])).
% 14.02/6.84  tff(c_32793, plain, (![A_2555, A_2556, C_2557]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_2555, A_2556, C_2557)) | ~m1_subset_1('#skF_1'(A_2555, A_2556, C_2557), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(A_2556, C_2557) | ~m1_subset_1(C_2557, k1_zfmisc_1(A_2555)) | ~m1_subset_1(A_2556, k1_zfmisc_1(A_2555)) | ~r1_tarski(A_2556, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_32784])).
% 14.02/6.84  tff(c_32894, plain, (![A_2576, A_2577, C_2578]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(A_2576, A_2577, C_2578)) | ~m1_subset_1('#skF_1'(A_2576, A_2577, C_2578), u1_struct_0('#skF_2')) | r1_tarski(A_2577, C_2578) | ~m1_subset_1(C_2578, k1_zfmisc_1(A_2576)) | ~m1_subset_1(A_2577, k1_zfmisc_1(A_2576)) | ~r1_tarski(A_2577, k1_tops_1('#skF_2', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_36, c_32793])).
% 14.02/6.84  tff(c_36411, plain, (![B_2806, C_2807]: (m1_connsp_2('#skF_4', '#skF_2', '#skF_1'(u1_struct_0('#skF_2'), B_2806, C_2807)) | ~r1_tarski(B_2806, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2806, C_2807) | ~m1_subset_1(C_2807, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2806, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_32894])).
% 14.02/6.84  tff(c_36426, plain, (![B_2806, C_2807]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2806, C_2807), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2806, C_2807), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(B_2806, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2806, C_2807) | ~m1_subset_1(C_2807, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2806, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_36411, c_26])).
% 14.02/6.84  tff(c_36449, plain, (![B_2806, C_2807]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2806, C_2807), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2806, C_2807), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(B_2806, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2806, C_2807) | ~m1_subset_1(C_2807, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2806, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_36426])).
% 14.02/6.84  tff(c_36455, plain, (![B_2808, C_2809]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2808, C_2809), '#skF_4') | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_2'), B_2808, C_2809), u1_struct_0('#skF_2')) | ~r1_tarski(B_2808, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2808, C_2809) | ~m1_subset_1(C_2809, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2808, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_36449])).
% 14.02/6.84  tff(c_36461, plain, (![B_2810, C_2811]: (r2_hidden('#skF_1'(u1_struct_0('#skF_2'), B_2810, C_2811), '#skF_4') | ~r1_tarski(B_2810, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2810, C_2811) | ~m1_subset_1(C_2811, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2810, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_8, c_36455])).
% 14.02/6.84  tff(c_36465, plain, (![B_2810]: (~r1_tarski(B_2810, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2810, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_2810, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_36461, c_4])).
% 14.02/6.84  tff(c_36472, plain, (![B_2812]: (~r1_tarski(B_2812, k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(B_2812, '#skF_4') | ~m1_subset_1(B_2812, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36465])).
% 14.02/6.84  tff(c_36487, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_29572, c_36472])).
% 14.02/6.84  tff(c_36515, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29635, c_36487])).
% 14.02/6.84  tff(c_36517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29085, c_36515])).
% 14.02/6.84  tff(c_36519, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_29084])).
% 14.02/6.84  tff(c_36781, plain, (![B_2854, A_2855, C_2856]: (r2_hidden(B_2854, k1_tops_1(A_2855, C_2856)) | ~m1_connsp_2(C_2856, A_2855, B_2854) | ~m1_subset_1(C_2856, k1_zfmisc_1(u1_struct_0(A_2855))) | ~m1_subset_1(B_2854, u1_struct_0(A_2855)) | ~l1_pre_topc(A_2855) | ~v2_pre_topc(A_2855) | v2_struct_0(A_2855))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.02/6.84  tff(c_36791, plain, (![B_2854]: (r2_hidden(B_2854, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2854) | ~m1_subset_1(B_2854, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_36781])).
% 14.02/6.84  tff(c_36797, plain, (![B_2854]: (r2_hidden(B_2854, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2854) | ~m1_subset_1(B_2854, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_36791])).
% 14.02/6.84  tff(c_36799, plain, (![B_2857]: (r2_hidden(B_2857, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_2857) | ~m1_subset_1(B_2857, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_36797])).
% 14.02/6.84  tff(c_22713, plain, (![A_1785, A_12]: (v3_pre_topc(k1_tops_1(A_1785, A_12), A_1785) | ~l1_pre_topc(A_1785) | ~v2_pre_topc(A_1785) | ~r1_tarski(A_12, u1_struct_0(A_1785)))), inference(resolution, [status(thm)], [c_12, c_22707])).
% 14.02/6.84  tff(c_36701, plain, (![A_2840]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_2840)) | ~r1_tarski(k1_tops_1('#skF_2', A_2840), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', A_2840), '#skF_2') | ~r1_tarski(A_2840, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_29061])).
% 14.02/6.84  tff(c_36709, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_22713, c_36701])).
% 14.02/6.84  tff(c_36718, plain, (![A_12]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_12)) | ~r1_tarski(k1_tops_1('#skF_2', A_12), '#skF_4') | ~r1_tarski(A_12, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_36709])).
% 14.02/6.84  tff(c_36803, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36799, c_36718])).
% 14.02/6.84  tff(c_36818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_22696, c_61, c_36519, c_36803])).
% 14.02/6.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.02/6.84  
% 14.02/6.84  Inference rules
% 14.02/6.84  ----------------------
% 14.02/6.84  #Ref     : 0
% 14.02/6.84  #Sup     : 7019
% 14.02/6.84  #Fact    : 0
% 14.02/6.84  #Define  : 0
% 14.02/6.84  #Split   : 104
% 14.02/6.84  #Chain   : 0
% 14.02/6.84  #Close   : 0
% 14.02/6.84  
% 14.02/6.84  Ordering : KBO
% 14.02/6.84  
% 14.02/6.84  Simplification rules
% 14.02/6.84  ----------------------
% 14.02/6.84  #Subsume      : 2637
% 14.02/6.84  #Demod        : 8494
% 14.02/6.84  #Tautology    : 1243
% 14.02/6.84  #SimpNegUnit  : 666
% 14.02/6.84  #BackRed      : 0
% 14.02/6.84  
% 14.02/6.84  #Partial instantiations: 0
% 14.02/6.84  #Strategies tried      : 1
% 14.02/6.84  
% 14.02/6.84  Timing (in seconds)
% 14.02/6.84  ----------------------
% 14.02/6.84  Preprocessing        : 0.31
% 14.02/6.84  Parsing              : 0.17
% 14.02/6.84  CNF conversion       : 0.03
% 14.02/6.84  Main loop            : 5.67
% 14.02/6.84  Inferencing          : 1.46
% 14.02/6.84  Reduction            : 1.70
% 14.02/6.84  Demodulation         : 1.17
% 14.02/6.84  BG Simplification    : 0.10
% 14.02/6.84  Subsumption          : 2.11
% 14.02/6.84  Abstraction          : 0.19
% 14.02/6.84  MUC search           : 0.00
% 14.02/6.84  Cooper               : 0.00
% 14.02/6.84  Total                : 6.10
% 14.02/6.84  Index Insertion      : 0.00
% 14.02/6.84  Index Deletion       : 0.00
% 14.02/6.84  Index Matching       : 0.00
% 14.02/6.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
