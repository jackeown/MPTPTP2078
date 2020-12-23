%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 378 expanded)
%              Number of leaves         :   27 ( 143 expanded)
%              Depth                    :   16
%              Number of atoms          :  469 (1607 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_144,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_53,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_55,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    ! [D_57] :
      ( ~ r2_hidden('#skF_2',D_57)
      | ~ r1_tarski(D_57,'#skF_3')
      | ~ v3_pre_topc(D_57,'#skF_1')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_225,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_14,plain,(
    ! [A_14,B_18,C_20] :
      ( r1_tarski(k1_tops_1(A_14,B_18),k1_tops_1(A_14,C_20))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_254,plain,(
    ! [B_112,A_113,C_114] :
      ( r2_hidden(B_112,k1_tops_1(A_113,C_114))
      | ~ m1_connsp_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_112,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_258,plain,(
    ! [B_112] :
      ( r2_hidden(B_112,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_66,c_254])).

tff(c_267,plain,(
    ! [B_112] :
      ( r2_hidden(B_112,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_258])).

tff(c_293,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,k1_tops_1('#skF_1','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_119)
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_267])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_314,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(B_122,A_123)
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_4'),k1_zfmisc_1(A_123))
      | ~ m1_connsp_2('#skF_4','#skF_1',B_122)
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_293,c_2])).

tff(c_337,plain,(
    ! [B_128,B_129] :
      ( r2_hidden(B_128,B_129)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_128)
      | ~ m1_subset_1(B_128,u1_struct_0('#skF_1'))
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_129) ) ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_340,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_2',B_129)
      | ~ m1_connsp_2('#skF_4','#skF_1','#skF_2')
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_129) ) ),
    inference(resolution,[status(thm)],[c_26,c_337])).

tff(c_341,plain,(
    ~ m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_342,plain,(
    ! [B_130,A_131,C_132] :
      ( m1_connsp_2(B_130,A_131,C_132)
      | ~ r2_hidden(C_132,B_130)
      | ~ v3_pre_topc(B_130,A_131)
      | ~ m1_subset_1(C_132,u1_struct_0(A_131))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_344,plain,(
    ! [B_130] :
      ( m1_connsp_2(B_130,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_130)
      | ~ v3_pre_topc(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_342])).

tff(c_347,plain,(
    ! [B_130] :
      ( m1_connsp_2(B_130,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_130)
      | ~ v3_pre_topc(B_130,'#skF_1')
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_344])).

tff(c_349,plain,(
    ! [B_133] :
      ( m1_connsp_2(B_133,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_133)
      | ~ v3_pre_topc(B_133,'#skF_1')
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_347])).

tff(c_356,plain,
    ( m1_connsp_2('#skF_4','#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_349])).

tff(c_369,plain,(
    m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54,c_356])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_369])).

tff(c_380,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_2',B_134)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_4'),B_134) ) ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_384,plain,(
    ! [C_20] :
      ( r2_hidden('#skF_2',k1_tops_1('#skF_1',C_20))
      | ~ r1_tarski('#skF_4',C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_380])).

tff(c_407,plain,(
    ! [C_135] :
      ( r2_hidden('#skF_2',k1_tops_1('#skF_1',C_135))
      | ~ r1_tarski('#skF_4',C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66,c_384])).

tff(c_421,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_407])).

tff(c_429,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_421])).

tff(c_16,plain,(
    ! [C_27,A_21,B_25] :
      ( m1_connsp_2(C_27,A_21,B_25)
      | ~ r2_hidden(B_25,k1_tops_1(A_21,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_431,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_429,c_16])).

tff(c_436,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_431])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_225,c_436])).

tff(c_441,plain,(
    ! [D_136] :
      ( ~ r2_hidden('#skF_2',D_136)
      | ~ r1_tarski(D_136,'#skF_3')
      | ~ v3_pre_topc(D_136,'#skF_1')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_448,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_441])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_448])).

tff(c_463,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_505,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k1_tops_1(A_146,B_147),B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_510,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_505])).

tff(c_514,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_510])).

tff(c_757,plain,(
    ! [B_198,A_199,C_200] :
      ( r2_hidden(B_198,k1_tops_1(A_199,C_200))
      | ~ m1_connsp_2(C_200,A_199,B_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_subset_1(B_198,u1_struct_0(A_199))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_764,plain,(
    ! [B_198] :
      ( r2_hidden(B_198,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_198)
      | ~ m1_subset_1(B_198,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_757])).

tff(c_769,plain,(
    ! [B_198] :
      ( r2_hidden(B_198,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_198)
      | ~ m1_subset_1(B_198,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_764])).

tff(c_771,plain,(
    ! [B_201] :
      ( r2_hidden(B_201,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_201)
      | ~ m1_subset_1(B_201,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_769])).

tff(c_539,plain,(
    ! [A_157,B_158] :
      ( v3_pre_topc(k1_tops_1(A_157,B_158),A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_545,plain,(
    ! [A_157,A_5] :
      ( v3_pre_topc(k1_tops_1(A_157,A_5),A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | ~ r1_tarski(A_5,u1_struct_0(A_157)) ) ),
    inference(resolution,[status(thm)],[c_6,c_539])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k1_tops_1(A_7,B_8),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_609,plain,(
    ! [D_177] :
      ( ~ r2_hidden('#skF_2',D_177)
      | ~ r1_tarski(D_177,'#skF_3')
      | ~ v3_pre_topc(D_177,'#skF_1')
      | ~ m1_subset_1(D_177,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_34])).

tff(c_613,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_609])).

tff(c_654,plain,(
    ! [B_186] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_186))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_186),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_186),'#skF_1')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_613])).

tff(c_682,plain,(
    ! [A_190] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_190))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_190),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_190),'#skF_1')
      | ~ r1_tarski(A_190,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_654])).

tff(c_690,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_545,c_682])).

tff(c_699,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_690])).

tff(c_777,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_771,c_699])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_463,c_60,c_514,c_777])).

tff(c_791,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_795,plain,(
    ! [A_204,B_205] :
      ( r1_tarski(A_204,B_205)
      | ~ m1_subset_1(A_204,k1_zfmisc_1(B_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_807,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_795])).

tff(c_856,plain,(
    ! [A_217,B_218] :
      ( r1_tarski(k1_tops_1(A_217,B_218),B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_863,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_856])).

tff(c_870,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_863])).

tff(c_1066,plain,(
    ! [B_251,A_252,C_253] :
      ( r2_hidden(B_251,k1_tops_1(A_252,C_253))
      | ~ m1_connsp_2(C_253,A_252,B_251)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ m1_subset_1(B_251,u1_struct_0(A_252))
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1075,plain,(
    ! [B_251] :
      ( r2_hidden(B_251,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_251)
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1066])).

tff(c_1084,plain,(
    ! [B_251] :
      ( r2_hidden(B_251,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_251)
      | ~ m1_subset_1(B_251,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1075])).

tff(c_1086,plain,(
    ! [B_254] :
      ( r2_hidden(B_254,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_254)
      | ~ m1_subset_1(B_254,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1084])).

tff(c_873,plain,(
    ! [A_221,B_222] :
      ( v3_pre_topc(k1_tops_1(A_221,B_222),A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_881,plain,(
    ! [A_221,A_5] :
      ( v3_pre_topc(k1_tops_1(A_221,A_5),A_221)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | ~ r1_tarski(A_5,u1_struct_0(A_221)) ) ),
    inference(resolution,[status(thm)],[c_6,c_873])).

tff(c_792,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_57] :
      ( ~ r2_hidden('#skF_2',D_57)
      | ~ r1_tarski(D_57,'#skF_3')
      | ~ v3_pre_topc(D_57,'#skF_1')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_905,plain,(
    ! [D_227] :
      ( ~ r2_hidden('#skF_2',D_227)
      | ~ r1_tarski(D_227,'#skF_3')
      | ~ v3_pre_topc(D_227,'#skF_1')
      | ~ m1_subset_1(D_227,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_42])).

tff(c_909,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_905])).

tff(c_989,plain,(
    ! [B_244] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_244))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_244),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_244),'#skF_1')
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_909])).

tff(c_1019,plain,(
    ! [A_245] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_245))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_245),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_245),'#skF_1')
      | ~ r1_tarski(A_245,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_989])).

tff(c_1027,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_881,c_1019])).

tff(c_1039,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1027])).

tff(c_1090,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1086,c_1039])).

tff(c_1099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_791,c_807,c_870,c_1090])).

tff(c_1100,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1104,plain,(
    ! [A_257,B_258] :
      ( r1_tarski(A_257,B_258)
      | ~ m1_subset_1(A_257,k1_zfmisc_1(B_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1112,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_1104])).

tff(c_1115,plain,(
    ! [A_262,B_263] :
      ( r1_tarski(k1_tops_1(A_262,B_263),B_263)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1120,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1115])).

tff(c_1124,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1120])).

tff(c_1398,plain,(
    ! [B_322,A_323,C_324] :
      ( r2_hidden(B_322,k1_tops_1(A_323,C_324))
      | ~ m1_connsp_2(C_324,A_323,B_322)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ m1_subset_1(B_322,u1_struct_0(A_323))
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1405,plain,(
    ! [B_322] :
      ( r2_hidden(B_322,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_322)
      | ~ m1_subset_1(B_322,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1398])).

tff(c_1410,plain,(
    ! [B_322] :
      ( r2_hidden(B_322,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_322)
      | ~ m1_subset_1(B_322,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1405])).

tff(c_1412,plain,(
    ! [B_325] :
      ( r2_hidden(B_325,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_325)
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1410])).

tff(c_1278,plain,(
    ! [A_298,B_299] :
      ( v3_pre_topc(k1_tops_1(A_298,B_299),A_298)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1284,plain,(
    ! [A_298,A_5] :
      ( v3_pre_topc(k1_tops_1(A_298,A_5),A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298)
      | ~ r1_tarski(A_5,u1_struct_0(A_298)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1278])).

tff(c_1101,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_57] :
      ( ~ r2_hidden('#skF_2',D_57)
      | ~ r1_tarski(D_57,'#skF_3')
      | ~ v3_pre_topc(D_57,'#skF_1')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1301,plain,(
    ! [D_304] :
      ( ~ r2_hidden('#skF_2',D_304)
      | ~ r1_tarski(D_304,'#skF_3')
      | ~ v3_pre_topc(D_304,'#skF_1')
      | ~ m1_subset_1(D_304,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1101,c_38])).

tff(c_1305,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1301])).

tff(c_1349,plain,(
    ! [B_318] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_318))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_318),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_318),'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1305])).

tff(c_1368,plain,(
    ! [A_319] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_319))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_319),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_319),'#skF_1')
      | ~ r1_tarski(A_319,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1349])).

tff(c_1376,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1284,c_1368])).

tff(c_1385,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1376])).

tff(c_1416,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1412,c_1385])).

tff(c_1425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1100,c_1112,c_1124,c_1416])).

tff(c_1426,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1428,plain,(
    ! [A_326,B_327] :
      ( r1_tarski(A_326,B_327)
      | ~ m1_subset_1(A_326,k1_zfmisc_1(B_327)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1432,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_1428])).

tff(c_1442,plain,(
    ! [A_333,B_334] :
      ( r1_tarski(k1_tops_1(A_333,B_334),B_334)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1447,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1442])).

tff(c_1451,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1447])).

tff(c_1958,plain,(
    ! [B_434,A_435,C_436] :
      ( r2_hidden(B_434,k1_tops_1(A_435,C_436))
      | ~ m1_connsp_2(C_436,A_435,B_434)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(u1_struct_0(A_435)))
      | ~ m1_subset_1(B_434,u1_struct_0(A_435))
      | ~ l1_pre_topc(A_435)
      | ~ v2_pre_topc(A_435)
      | v2_struct_0(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1965,plain,(
    ! [B_434] :
      ( r2_hidden(B_434,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_434)
      | ~ m1_subset_1(B_434,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_1958])).

tff(c_1970,plain,(
    ! [B_434] :
      ( r2_hidden(B_434,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_434)
      | ~ m1_subset_1(B_434,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1965])).

tff(c_1972,plain,(
    ! [B_437] :
      ( r2_hidden(B_437,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_437)
      | ~ m1_subset_1(B_437,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1970])).

tff(c_1603,plain,(
    ! [A_365,B_366] :
      ( v3_pre_topc(k1_tops_1(A_365,B_366),A_365)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1612,plain,(
    ! [A_365,A_5] :
      ( v3_pre_topc(k1_tops_1(A_365,A_5),A_365)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | ~ r1_tarski(A_5,u1_struct_0(A_365)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1603])).

tff(c_1427,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_57] :
      ( ~ r2_hidden('#skF_2',D_57)
      | ~ r1_tarski(D_57,'#skF_3')
      | ~ v3_pre_topc(D_57,'#skF_1')
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1747,plain,(
    ! [D_391] :
      ( ~ r2_hidden('#skF_2',D_391)
      | ~ r1_tarski(D_391,'#skF_3')
      | ~ v3_pre_topc(D_391,'#skF_1')
      | ~ m1_subset_1(D_391,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1427,c_46])).

tff(c_1751,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_8))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_8),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_8),'#skF_1')
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_1747])).

tff(c_1855,plain,(
    ! [B_415] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_415))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_415),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_415),'#skF_1')
      | ~ m1_subset_1(B_415,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1751])).

tff(c_1928,plain,(
    ! [A_432] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_432))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_432),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',A_432),'#skF_1')
      | ~ r1_tarski(A_432,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_1855])).

tff(c_1936,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_1612,c_1928])).

tff(c_1945,plain,(
    ! [A_5] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_5))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_5),'#skF_3')
      | ~ r1_tarski(A_5,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1936])).

tff(c_1976,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1972,c_1945])).

tff(c_1985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1426,c_1432,c_1451,c_1976])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:19:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  
% 4.46/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.46/1.78  
% 4.46/1.78  %Foreground sorts:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Background operators:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Foreground operators:
% 4.46/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.46/1.78  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.46/1.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.46/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.78  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.46/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.78  
% 4.64/1.81  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 4.64/1.81  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 4.64/1.81  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.64/1.81  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.64/1.81  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.64/1.81  tff(f_119, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.64/1.81  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.64/1.81  tff(f_50, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.64/1.81  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.64/1.81  tff(c_26, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_48, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_53, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 4.64/1.81  tff(c_44, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_55, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 4.64/1.81  tff(c_40, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_54, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 4.64/1.81  tff(c_52, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_52])).
% 4.64/1.81  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_34, plain, (![D_57]: (~r2_hidden('#skF_2', D_57) | ~r1_tarski(D_57, '#skF_3') | ~v3_pre_topc(D_57, '#skF_1') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_225, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_34])).
% 4.64/1.81  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_14, plain, (![A_14, B_18, C_20]: (r1_tarski(k1_tops_1(A_14, B_18), k1_tops_1(A_14, C_20)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.64/1.81  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.81  tff(c_254, plain, (![B_112, A_113, C_114]: (r2_hidden(B_112, k1_tops_1(A_113, C_114)) | ~m1_connsp_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_112, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_258, plain, (![B_112]: (r2_hidden(B_112, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_112) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_66, c_254])).
% 4.64/1.81  tff(c_267, plain, (![B_112]: (r2_hidden(B_112, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_112) | ~m1_subset_1(B_112, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_258])).
% 4.64/1.81  tff(c_293, plain, (![B_119]: (r2_hidden(B_119, k1_tops_1('#skF_1', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_1', B_119) | ~m1_subset_1(B_119, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_267])).
% 4.64/1.81  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.64/1.81  tff(c_314, plain, (![B_122, A_123]: (r2_hidden(B_122, A_123) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_4'), k1_zfmisc_1(A_123)) | ~m1_connsp_2('#skF_4', '#skF_1', B_122) | ~m1_subset_1(B_122, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_293, c_2])).
% 4.64/1.81  tff(c_337, plain, (![B_128, B_129]: (r2_hidden(B_128, B_129) | ~m1_connsp_2('#skF_4', '#skF_1', B_128) | ~m1_subset_1(B_128, u1_struct_0('#skF_1')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_129))), inference(resolution, [status(thm)], [c_6, c_314])).
% 4.64/1.81  tff(c_340, plain, (![B_129]: (r2_hidden('#skF_2', B_129) | ~m1_connsp_2('#skF_4', '#skF_1', '#skF_2') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_129))), inference(resolution, [status(thm)], [c_26, c_337])).
% 4.64/1.81  tff(c_341, plain, (~m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_340])).
% 4.64/1.81  tff(c_342, plain, (![B_130, A_131, C_132]: (m1_connsp_2(B_130, A_131, C_132) | ~r2_hidden(C_132, B_130) | ~v3_pre_topc(B_130, A_131) | ~m1_subset_1(C_132, u1_struct_0(A_131)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.64/1.81  tff(c_344, plain, (![B_130]: (m1_connsp_2(B_130, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_130) | ~v3_pre_topc(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_342])).
% 4.64/1.81  tff(c_347, plain, (![B_130]: (m1_connsp_2(B_130, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_130) | ~v3_pre_topc(B_130, '#skF_1') | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_344])).
% 4.64/1.81  tff(c_349, plain, (![B_133]: (m1_connsp_2(B_133, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_133) | ~v3_pre_topc(B_133, '#skF_1') | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_347])).
% 4.64/1.81  tff(c_356, plain, (m1_connsp_2('#skF_4', '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_349])).
% 4.64/1.81  tff(c_369, plain, (m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_54, c_356])).
% 4.64/1.81  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_341, c_369])).
% 4.64/1.81  tff(c_380, plain, (![B_134]: (r2_hidden('#skF_2', B_134) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_4'), B_134))), inference(splitRight, [status(thm)], [c_340])).
% 4.64/1.81  tff(c_384, plain, (![C_20]: (r2_hidden('#skF_2', k1_tops_1('#skF_1', C_20)) | ~r1_tarski('#skF_4', C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_380])).
% 4.64/1.81  tff(c_407, plain, (![C_135]: (r2_hidden('#skF_2', k1_tops_1('#skF_1', C_135)) | ~r1_tarski('#skF_4', C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_66, c_384])).
% 4.64/1.81  tff(c_421, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_407])).
% 4.64/1.81  tff(c_429, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_421])).
% 4.64/1.81  tff(c_16, plain, (![C_27, A_21, B_25]: (m1_connsp_2(C_27, A_21, B_25) | ~r2_hidden(B_25, k1_tops_1(A_21, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_431, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_429, c_16])).
% 4.64/1.81  tff(c_436, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_431])).
% 4.64/1.81  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_225, c_436])).
% 4.64/1.81  tff(c_441, plain, (![D_136]: (~r2_hidden('#skF_2', D_136) | ~r1_tarski(D_136, '#skF_3') | ~v3_pre_topc(D_136, '#skF_1') | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_34])).
% 4.64/1.81  tff(c_448, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_441])).
% 4.64/1.81  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_448])).
% 4.64/1.81  tff(c_463, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 4.64/1.81  tff(c_56, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.81  tff(c_60, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 4.64/1.81  tff(c_505, plain, (![A_146, B_147]: (r1_tarski(k1_tops_1(A_146, B_147), B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.64/1.81  tff(c_510, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_505])).
% 4.64/1.81  tff(c_514, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_510])).
% 4.64/1.81  tff(c_757, plain, (![B_198, A_199, C_200]: (r2_hidden(B_198, k1_tops_1(A_199, C_200)) | ~m1_connsp_2(C_200, A_199, B_198) | ~m1_subset_1(C_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_subset_1(B_198, u1_struct_0(A_199)) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_764, plain, (![B_198]: (r2_hidden(B_198, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_198) | ~m1_subset_1(B_198, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_757])).
% 4.64/1.81  tff(c_769, plain, (![B_198]: (r2_hidden(B_198, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_198) | ~m1_subset_1(B_198, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_764])).
% 4.64/1.81  tff(c_771, plain, (![B_201]: (r2_hidden(B_201, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_201) | ~m1_subset_1(B_201, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_769])).
% 4.64/1.81  tff(c_539, plain, (![A_157, B_158]: (v3_pre_topc(k1_tops_1(A_157, B_158), A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.64/1.81  tff(c_545, plain, (![A_157, A_5]: (v3_pre_topc(k1_tops_1(A_157, A_5), A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | ~r1_tarski(A_5, u1_struct_0(A_157)))), inference(resolution, [status(thm)], [c_6, c_539])).
% 4.64/1.81  tff(c_8, plain, (![A_7, B_8]: (m1_subset_1(k1_tops_1(A_7, B_8), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.64/1.81  tff(c_609, plain, (![D_177]: (~r2_hidden('#skF_2', D_177) | ~r1_tarski(D_177, '#skF_3') | ~v3_pre_topc(D_177, '#skF_1') | ~m1_subset_1(D_177, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_34])).
% 4.64/1.81  tff(c_613, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_609])).
% 4.64/1.81  tff(c_654, plain, (![B_186]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_186)) | ~r1_tarski(k1_tops_1('#skF_1', B_186), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_186), '#skF_1') | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_613])).
% 4.64/1.81  tff(c_682, plain, (![A_190]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_190)) | ~r1_tarski(k1_tops_1('#skF_1', A_190), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_190), '#skF_1') | ~r1_tarski(A_190, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_654])).
% 4.64/1.81  tff(c_690, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_545, c_682])).
% 4.64/1.81  tff(c_699, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_690])).
% 4.64/1.81  tff(c_777, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_771, c_699])).
% 4.64/1.81  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_463, c_60, c_514, c_777])).
% 4.64/1.81  tff(c_791, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 4.64/1.81  tff(c_795, plain, (![A_204, B_205]: (r1_tarski(A_204, B_205) | ~m1_subset_1(A_204, k1_zfmisc_1(B_205)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.81  tff(c_807, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_795])).
% 4.64/1.81  tff(c_856, plain, (![A_217, B_218]: (r1_tarski(k1_tops_1(A_217, B_218), B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.64/1.81  tff(c_863, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_856])).
% 4.64/1.81  tff(c_870, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_863])).
% 4.64/1.81  tff(c_1066, plain, (![B_251, A_252, C_253]: (r2_hidden(B_251, k1_tops_1(A_252, C_253)) | ~m1_connsp_2(C_253, A_252, B_251) | ~m1_subset_1(C_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~m1_subset_1(B_251, u1_struct_0(A_252)) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_1075, plain, (![B_251]: (r2_hidden(B_251, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_251) | ~m1_subset_1(B_251, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1066])).
% 4.64/1.81  tff(c_1084, plain, (![B_251]: (r2_hidden(B_251, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_251) | ~m1_subset_1(B_251, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1075])).
% 4.64/1.81  tff(c_1086, plain, (![B_254]: (r2_hidden(B_254, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_254) | ~m1_subset_1(B_254, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1084])).
% 4.64/1.81  tff(c_873, plain, (![A_221, B_222]: (v3_pre_topc(k1_tops_1(A_221, B_222), A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.64/1.81  tff(c_881, plain, (![A_221, A_5]: (v3_pre_topc(k1_tops_1(A_221, A_5), A_221) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | ~r1_tarski(A_5, u1_struct_0(A_221)))), inference(resolution, [status(thm)], [c_6, c_873])).
% 4.64/1.81  tff(c_792, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.64/1.81  tff(c_42, plain, (![D_57]: (~r2_hidden('#skF_2', D_57) | ~r1_tarski(D_57, '#skF_3') | ~v3_pre_topc(D_57, '#skF_1') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_905, plain, (![D_227]: (~r2_hidden('#skF_2', D_227) | ~r1_tarski(D_227, '#skF_3') | ~v3_pre_topc(D_227, '#skF_1') | ~m1_subset_1(D_227, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_792, c_42])).
% 4.64/1.81  tff(c_909, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_905])).
% 4.64/1.81  tff(c_989, plain, (![B_244]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_244)) | ~r1_tarski(k1_tops_1('#skF_1', B_244), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_244), '#skF_1') | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_909])).
% 4.64/1.81  tff(c_1019, plain, (![A_245]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_245)) | ~r1_tarski(k1_tops_1('#skF_1', A_245), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_245), '#skF_1') | ~r1_tarski(A_245, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_989])).
% 4.64/1.81  tff(c_1027, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_881, c_1019])).
% 4.64/1.81  tff(c_1039, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1027])).
% 4.64/1.81  tff(c_1090, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1086, c_1039])).
% 4.64/1.81  tff(c_1099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_791, c_807, c_870, c_1090])).
% 4.64/1.81  tff(c_1100, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.64/1.81  tff(c_1104, plain, (![A_257, B_258]: (r1_tarski(A_257, B_258) | ~m1_subset_1(A_257, k1_zfmisc_1(B_258)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.81  tff(c_1112, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1104])).
% 4.64/1.81  tff(c_1115, plain, (![A_262, B_263]: (r1_tarski(k1_tops_1(A_262, B_263), B_263) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.64/1.81  tff(c_1120, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1115])).
% 4.64/1.81  tff(c_1124, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1120])).
% 4.64/1.81  tff(c_1398, plain, (![B_322, A_323, C_324]: (r2_hidden(B_322, k1_tops_1(A_323, C_324)) | ~m1_connsp_2(C_324, A_323, B_322) | ~m1_subset_1(C_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~m1_subset_1(B_322, u1_struct_0(A_323)) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_1405, plain, (![B_322]: (r2_hidden(B_322, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_322) | ~m1_subset_1(B_322, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1398])).
% 4.64/1.81  tff(c_1410, plain, (![B_322]: (r2_hidden(B_322, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_322) | ~m1_subset_1(B_322, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1405])).
% 4.64/1.81  tff(c_1412, plain, (![B_325]: (r2_hidden(B_325, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_325) | ~m1_subset_1(B_325, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1410])).
% 4.64/1.81  tff(c_1278, plain, (![A_298, B_299]: (v3_pre_topc(k1_tops_1(A_298, B_299), A_298) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_298))) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.64/1.81  tff(c_1284, plain, (![A_298, A_5]: (v3_pre_topc(k1_tops_1(A_298, A_5), A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298) | ~r1_tarski(A_5, u1_struct_0(A_298)))), inference(resolution, [status(thm)], [c_6, c_1278])).
% 4.64/1.81  tff(c_1101, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.64/1.81  tff(c_38, plain, (![D_57]: (~r2_hidden('#skF_2', D_57) | ~r1_tarski(D_57, '#skF_3') | ~v3_pre_topc(D_57, '#skF_1') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_1301, plain, (![D_304]: (~r2_hidden('#skF_2', D_304) | ~r1_tarski(D_304, '#skF_3') | ~v3_pre_topc(D_304, '#skF_1') | ~m1_subset_1(D_304, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1101, c_38])).
% 4.64/1.81  tff(c_1305, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1301])).
% 4.64/1.81  tff(c_1349, plain, (![B_318]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_318)) | ~r1_tarski(k1_tops_1('#skF_1', B_318), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_318), '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1305])).
% 4.64/1.81  tff(c_1368, plain, (![A_319]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_319)) | ~r1_tarski(k1_tops_1('#skF_1', A_319), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_319), '#skF_1') | ~r1_tarski(A_319, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1349])).
% 4.64/1.81  tff(c_1376, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1284, c_1368])).
% 4.64/1.81  tff(c_1385, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1376])).
% 4.64/1.81  tff(c_1416, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1412, c_1385])).
% 4.64/1.81  tff(c_1425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1100, c_1112, c_1124, c_1416])).
% 4.64/1.81  tff(c_1426, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.64/1.81  tff(c_1428, plain, (![A_326, B_327]: (r1_tarski(A_326, B_327) | ~m1_subset_1(A_326, k1_zfmisc_1(B_327)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.64/1.81  tff(c_1432, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1428])).
% 4.64/1.81  tff(c_1442, plain, (![A_333, B_334]: (r1_tarski(k1_tops_1(A_333, B_334), B_334) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.64/1.81  tff(c_1447, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1442])).
% 4.64/1.81  tff(c_1451, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1447])).
% 4.64/1.81  tff(c_1958, plain, (![B_434, A_435, C_436]: (r2_hidden(B_434, k1_tops_1(A_435, C_436)) | ~m1_connsp_2(C_436, A_435, B_434) | ~m1_subset_1(C_436, k1_zfmisc_1(u1_struct_0(A_435))) | ~m1_subset_1(B_434, u1_struct_0(A_435)) | ~l1_pre_topc(A_435) | ~v2_pre_topc(A_435) | v2_struct_0(A_435))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.64/1.81  tff(c_1965, plain, (![B_434]: (r2_hidden(B_434, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_434) | ~m1_subset_1(B_434, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_1958])).
% 4.64/1.81  tff(c_1970, plain, (![B_434]: (r2_hidden(B_434, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_434) | ~m1_subset_1(B_434, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1965])).
% 4.64/1.81  tff(c_1972, plain, (![B_437]: (r2_hidden(B_437, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_437) | ~m1_subset_1(B_437, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1970])).
% 4.64/1.81  tff(c_1603, plain, (![A_365, B_366]: (v3_pre_topc(k1_tops_1(A_365, B_366), A_365) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.64/1.81  tff(c_1612, plain, (![A_365, A_5]: (v3_pre_topc(k1_tops_1(A_365, A_5), A_365) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | ~r1_tarski(A_5, u1_struct_0(A_365)))), inference(resolution, [status(thm)], [c_6, c_1603])).
% 4.64/1.81  tff(c_1427, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 4.64/1.81  tff(c_46, plain, (![D_57]: (~r2_hidden('#skF_2', D_57) | ~r1_tarski(D_57, '#skF_3') | ~v3_pre_topc(D_57, '#skF_1') | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.64/1.81  tff(c_1747, plain, (![D_391]: (~r2_hidden('#skF_2', D_391) | ~r1_tarski(D_391, '#skF_3') | ~v3_pre_topc(D_391, '#skF_1') | ~m1_subset_1(D_391, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_1427, c_46])).
% 4.64/1.81  tff(c_1751, plain, (![B_8]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_8)) | ~r1_tarski(k1_tops_1('#skF_1', B_8), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_8), '#skF_1') | ~m1_subset_1(B_8, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_1747])).
% 4.64/1.81  tff(c_1855, plain, (![B_415]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_415)) | ~r1_tarski(k1_tops_1('#skF_1', B_415), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_415), '#skF_1') | ~m1_subset_1(B_415, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1751])).
% 4.64/1.81  tff(c_1928, plain, (![A_432]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_432)) | ~r1_tarski(k1_tops_1('#skF_1', A_432), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', A_432), '#skF_1') | ~r1_tarski(A_432, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_1855])).
% 4.64/1.81  tff(c_1936, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1612, c_1928])).
% 4.64/1.81  tff(c_1945, plain, (![A_5]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_5)) | ~r1_tarski(k1_tops_1('#skF_1', A_5), '#skF_3') | ~r1_tarski(A_5, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1936])).
% 4.64/1.81  tff(c_1976, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1972, c_1945])).
% 4.64/1.81  tff(c_1985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1426, c_1432, c_1451, c_1976])).
% 4.64/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.81  
% 4.64/1.81  Inference rules
% 4.64/1.81  ----------------------
% 4.64/1.81  #Ref     : 0
% 4.64/1.81  #Sup     : 340
% 4.64/1.81  #Fact    : 0
% 4.64/1.81  #Define  : 0
% 4.64/1.81  #Split   : 19
% 4.64/1.81  #Chain   : 0
% 4.64/1.81  #Close   : 0
% 4.64/1.81  
% 4.64/1.81  Ordering : KBO
% 4.64/1.81  
% 4.64/1.81  Simplification rules
% 4.64/1.81  ----------------------
% 4.64/1.81  #Subsume      : 66
% 4.64/1.81  #Demod        : 303
% 4.64/1.81  #Tautology    : 51
% 4.64/1.81  #SimpNegUnit  : 33
% 4.64/1.81  #BackRed      : 0
% 4.64/1.81  
% 4.64/1.81  #Partial instantiations: 0
% 4.64/1.81  #Strategies tried      : 1
% 4.64/1.81  
% 4.64/1.81  Timing (in seconds)
% 4.64/1.81  ----------------------
% 4.64/1.81  Preprocessing        : 0.32
% 4.64/1.81  Parsing              : 0.17
% 4.64/1.81  CNF conversion       : 0.03
% 4.64/1.81  Main loop            : 0.66
% 4.64/1.81  Inferencing          : 0.26
% 4.64/1.81  Reduction            : 0.18
% 4.64/1.81  Demodulation         : 0.12
% 4.64/1.81  BG Simplification    : 0.02
% 4.64/1.81  Subsumption          : 0.14
% 4.64/1.81  Abstraction          : 0.02
% 4.64/1.81  MUC search           : 0.00
% 4.64/1.81  Cooper               : 0.00
% 4.64/1.81  Total                : 1.06
% 4.64/1.81  Index Insertion      : 0.00
% 4.64/1.81  Index Deletion       : 0.00
% 4.64/1.81  Index Matching       : 0.00
% 4.64/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
