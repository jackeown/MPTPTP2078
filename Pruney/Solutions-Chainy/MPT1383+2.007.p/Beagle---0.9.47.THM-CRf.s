%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:12 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 653 expanded)
%              Number of leaves         :   27 ( 235 expanded)
%              Depth                    :   18
%              Number of atoms          :  518 (2478 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
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

tff(f_124,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_99,axiom,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

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

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_55,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1296,plain,(
    ! [C_181,B_182,A_183] :
      ( r2_hidden(C_181,B_182)
      | ~ r2_hidden(C_181,A_183)
      | ~ r1_tarski(A_183,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1377,plain,(
    ! [A_195,B_196,B_197] :
      ( r2_hidden('#skF_1'(A_195,B_196),B_197)
      | ~ r1_tarski(A_195,B_197)
      | r1_tarski(A_195,B_196) ) ),
    inference(resolution,[status(thm)],[c_6,c_1296])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1398,plain,(
    ! [A_202,B_203,B_204,B_205] :
      ( r2_hidden('#skF_1'(A_202,B_203),B_204)
      | ~ r1_tarski(B_205,B_204)
      | ~ r1_tarski(A_202,B_205)
      | r1_tarski(A_202,B_203) ) ),
    inference(resolution,[status(thm)],[c_1377,c_2])).

tff(c_1461,plain,(
    ! [A_211,B_212] :
      ( r2_hidden('#skF_1'(A_211,B_212),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_211,'#skF_4')
      | r1_tarski(A_211,B_212) ) ),
    inference(resolution,[status(thm)],[c_60,c_1398])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1470,plain,(
    ! [A_213] :
      ( ~ r1_tarski(A_213,'#skF_4')
      | r1_tarski(A_213,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1461,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_53,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_34,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_268,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_184,plain,(
    ! [A_76,B_77] :
      ( v3_pre_topc(k1_tops_1(A_76,B_77),A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_198,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_191])).

tff(c_67,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),A_59)
      | r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_59] : r1_tarski(A_59,A_59) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_113,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tops_1(A_68,B_69),B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_127,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_80,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_199,plain,(
    ! [A_78,B_79,B_80] :
      ( r2_hidden('#skF_1'(A_78,B_79),B_80)
      | ~ r1_tarski(A_78,B_80)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_210,plain,(
    ! [A_83,B_84,B_85,B_86] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_85)
      | ~ r1_tarski(B_86,B_85)
      | ~ r1_tarski(A_83,B_86)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_281,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_91,'#skF_4')
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_60,c_210])).

tff(c_291,plain,(
    ! [A_93] :
      ( ~ r1_tarski(A_93,'#skF_4')
      | r1_tarski(A_93,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_281,c_4])).

tff(c_206,plain,(
    ! [A_78,B_79,B_2,B_80] :
      ( r2_hidden('#skF_1'(A_78,B_79),B_2)
      | ~ r1_tarski(B_80,B_2)
      | ~ r1_tarski(A_78,B_80)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_199,c_2])).

tff(c_833,plain,(
    ! [A_157,B_158,A_159] :
      ( r2_hidden('#skF_1'(A_157,B_158),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_157,A_159)
      | r1_tarski(A_157,B_158)
      | ~ r1_tarski(A_159,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_291,c_206])).

tff(c_857,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_4'),B_158),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_158)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_833])).

tff(c_943,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_4'),B_164),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_857])).

tff(c_951,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_943,c_4])).

tff(c_734,plain,(
    ! [B_146,A_147,C_148] :
      ( m1_connsp_2(B_146,A_147,C_148)
      | ~ r2_hidden(C_148,B_146)
      | ~ v3_pre_topc(B_146,A_147)
      | ~ m1_subset_1(C_148,u1_struct_0(A_147))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_736,plain,(
    ! [B_146] :
      ( m1_connsp_2(B_146,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_146)
      | ~ v3_pre_topc(B_146,'#skF_2')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_734])).

tff(c_739,plain,(
    ! [B_146] :
      ( m1_connsp_2(B_146,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_146)
      | ~ v3_pre_topc(B_146,'#skF_2')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_736])).

tff(c_741,plain,(
    ! [B_149] :
      ( m1_connsp_2(B_149,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_149)
      | ~ v3_pre_topc(B_149,'#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_739])).

tff(c_755,plain,(
    ! [A_6] :
      ( m1_connsp_2(A_6,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',A_6)
      | ~ v3_pre_topc(A_6,'#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_741])).

tff(c_956,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_951,c_755])).

tff(c_968,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_956])).

tff(c_975,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_968])).

tff(c_16,plain,(
    ! [A_13,B_17,C_19] :
      ( r1_tarski(k1_tops_1(A_13,B_17),k1_tops_1(A_13,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_78,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_8])).

tff(c_744,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_741])).

tff(c_754,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54,c_744])).

tff(c_476,plain,(
    ! [B_114,A_115,C_116] :
      ( r2_hidden(B_114,k1_tops_1(A_115,C_116))
      | ~ m1_connsp_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_114,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_488,plain,(
    ! [B_114,A_115,A_6] :
      ( r2_hidden(B_114,k1_tops_1(A_115,A_6))
      | ~ m1_connsp_2(A_6,A_115,B_114)
      | ~ m1_subset_1(B_114,u1_struct_0(A_115))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ r1_tarski(A_6,u1_struct_0(A_115)) ) ),
    inference(resolution,[status(thm)],[c_10,c_476])).

tff(c_186,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_184])).

tff(c_194,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_186])).

tff(c_115,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_113])).

tff(c_123,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_115])).

tff(c_855,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_5'),B_158),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_158)
      | ~ r1_tarski('#skF_5','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_123,c_833])).

tff(c_1082,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_1'(k1_tops_1('#skF_2','#skF_5'),B_175),u1_struct_0('#skF_2'))
      | r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_855])).

tff(c_1090,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1082,c_4])).

tff(c_1097,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_5'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1090,c_755])).

tff(c_1108,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_5'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_1097])).

tff(c_1114,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1108])).

tff(c_1137,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_488,c_1114])).

tff(c_1149,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_30,c_28,c_26,c_754,c_1137])).

tff(c_1151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1149])).

tff(c_1153,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1108])).

tff(c_1163,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_3',B_178)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_178) ) ),
    inference(resolution,[status(thm)],[c_1153,c_2])).

tff(c_1182,plain,(
    ! [C_19] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_19))
      | ~ r1_tarski('#skF_5',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_1163])).

tff(c_1241,plain,(
    ! [C_179] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_179))
      | ~ r1_tarski('#skF_5',C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_74,c_1182])).

tff(c_1251,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1241])).

tff(c_1258,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1251])).

tff(c_1260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_1258])).

tff(c_1262,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_968])).

tff(c_18,plain,(
    ! [C_26,A_20,B_24] :
      ( m1_connsp_2(C_26,A_20,B_24)
      | ~ r2_hidden(B_24,k1_tops_1(A_20,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1264,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1262,c_18])).

tff(c_1269,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_1264])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_268,c_1269])).

tff(c_1274,plain,(
    ! [D_180] :
      ( ~ r2_hidden('#skF_3',D_180)
      | ~ r1_tarski(D_180,'#skF_4')
      | ~ v3_pre_topc(D_180,'#skF_2')
      | ~ m1_subset_1(D_180,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1277,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_1274])).

tff(c_1288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_1277])).

tff(c_1290,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1294,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_1290])).

tff(c_1483,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1470,c_1294])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1483])).

tff(c_1495,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1498,plain,(
    ! [A_216,B_217] :
      ( r1_tarski(A_216,B_217)
      | ~ m1_subset_1(A_216,k1_zfmisc_1(B_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1506,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1498])).

tff(c_1523,plain,(
    ! [A_226,B_227] :
      ( r1_tarski(k1_tops_1(A_226,B_227),B_227)
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1528,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1523])).

tff(c_1532,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1528])).

tff(c_1808,plain,(
    ! [B_272,A_273,C_274] :
      ( r2_hidden(B_272,k1_tops_1(A_273,C_274))
      | ~ m1_connsp_2(C_274,A_273,B_272)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(B_272,u1_struct_0(A_273))
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1813,plain,(
    ! [B_272] :
      ( r2_hidden(B_272,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_272)
      | ~ m1_subset_1(B_272,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1808])).

tff(c_1817,plain,(
    ! [B_272] :
      ( r2_hidden(B_272,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_272)
      | ~ m1_subset_1(B_272,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1813])).

tff(c_1819,plain,(
    ! [B_275] :
      ( r2_hidden(B_275,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_275)
      | ~ m1_subset_1(B_275,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1817])).

tff(c_1562,plain,(
    ! [A_236,B_237] :
      ( v3_pre_topc(k1_tops_1(A_236,B_237),A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1568,plain,(
    ! [A_236,A_6] :
      ( v3_pre_topc(k1_tops_1(A_236,A_6),A_236)
      | ~ l1_pre_topc(A_236)
      | ~ v2_pre_topc(A_236)
      | ~ r1_tarski(A_6,u1_struct_0(A_236)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1562])).

tff(c_1516,plain,(
    ! [C_223,B_224,A_225] :
      ( r2_hidden(C_223,B_224)
      | ~ r2_hidden(C_223,A_225)
      | ~ r1_tarski(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1549,plain,(
    ! [A_231,B_232,B_233] :
      ( r2_hidden('#skF_1'(A_231,B_232),B_233)
      | ~ r1_tarski(A_231,B_233)
      | r1_tarski(A_231,B_232) ) ),
    inference(resolution,[status(thm)],[c_6,c_1516])).

tff(c_1574,plain,(
    ! [A_240,B_241,B_242,B_243] :
      ( r2_hidden('#skF_1'(A_240,B_241),B_242)
      | ~ r1_tarski(B_243,B_242)
      | ~ r1_tarski(A_240,B_243)
      | r1_tarski(A_240,B_241) ) ),
    inference(resolution,[status(thm)],[c_1549,c_2])).

tff(c_1601,plain,(
    ! [A_245,B_246] :
      ( r2_hidden('#skF_1'(A_245,B_246),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_245,'#skF_4')
      | r1_tarski(A_245,B_246) ) ),
    inference(resolution,[status(thm)],[c_1506,c_1574])).

tff(c_1609,plain,(
    ! [A_245] :
      ( ~ r1_tarski(A_245,'#skF_4')
      | r1_tarski(A_245,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1601,c_4])).

tff(c_1496,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1588,plain,(
    ! [D_244] :
      ( ~ r2_hidden('#skF_3',D_244)
      | ~ r1_tarski(D_244,'#skF_4')
      | ~ v3_pre_topc(D_244,'#skF_2')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1496,c_42])).

tff(c_1629,plain,(
    ! [A_249] :
      ( ~ r2_hidden('#skF_3',A_249)
      | ~ r1_tarski(A_249,'#skF_4')
      | ~ v3_pre_topc(A_249,'#skF_2')
      | ~ r1_tarski(A_249,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1588])).

tff(c_1650,plain,(
    ! [A_250] :
      ( ~ r2_hidden('#skF_3',A_250)
      | ~ v3_pre_topc(A_250,'#skF_2')
      | ~ r1_tarski(A_250,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1609,c_1629])).

tff(c_1654,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1568,c_1650])).

tff(c_1663,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1654])).

tff(c_1823,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1819,c_1663])).

tff(c_1836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1495,c_1506,c_1532,c_1823])).

tff(c_1837,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1840,plain,(
    ! [A_276,B_277] :
      ( r1_tarski(A_276,B_277)
      | ~ m1_subset_1(A_276,k1_zfmisc_1(B_277)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1844,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1840])).

tff(c_2248,plain,(
    ! [A_350,B_351] :
      ( r1_tarski(k1_tops_1(A_350,B_351),B_351)
      | ~ m1_subset_1(B_351,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2253,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2248])).

tff(c_2257,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2253])).

tff(c_2523,plain,(
    ! [B_395,A_396,C_397] :
      ( r2_hidden(B_395,k1_tops_1(A_396,C_397))
      | ~ m1_connsp_2(C_397,A_396,B_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ m1_subset_1(B_395,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2528,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2523])).

tff(c_2532,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2528])).

tff(c_2558,plain,(
    ! [B_401] :
      ( r2_hidden(B_401,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_401)
      | ~ m1_subset_1(B_401,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2532])).

tff(c_2259,plain,(
    ! [A_354,B_355] :
      ( v3_pre_topc(k1_tops_1(A_354,B_355),A_354)
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2265,plain,(
    ! [A_354,A_6] :
      ( v3_pre_topc(k1_tops_1(A_354,A_6),A_354)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | ~ r1_tarski(A_6,u1_struct_0(A_354)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2259])).

tff(c_1857,plain,(
    ! [C_284,B_285,A_286] :
      ( r2_hidden(C_284,B_285)
      | ~ r2_hidden(C_284,A_286)
      | ~ r1_tarski(A_286,B_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1863,plain,(
    ! [A_288,B_289,B_290] :
      ( r2_hidden('#skF_1'(A_288,B_289),B_290)
      | ~ r1_tarski(A_288,B_290)
      | r1_tarski(A_288,B_289) ) ),
    inference(resolution,[status(thm)],[c_6,c_1857])).

tff(c_2304,plain,(
    ! [A_360,B_361,B_362,B_363] :
      ( r2_hidden('#skF_1'(A_360,B_361),B_362)
      | ~ r1_tarski(B_363,B_362)
      | ~ r1_tarski(A_360,B_363)
      | r1_tarski(A_360,B_361) ) ),
    inference(resolution,[status(thm)],[c_1863,c_2])).

tff(c_2345,plain,(
    ! [A_368,B_369] :
      ( r2_hidden('#skF_1'(A_368,B_369),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_368,'#skF_4')
      | r1_tarski(A_368,B_369) ) ),
    inference(resolution,[status(thm)],[c_1844,c_2304])).

tff(c_2354,plain,(
    ! [A_370] :
      ( ~ r1_tarski(A_370,'#skF_4')
      | r1_tarski(A_370,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2345,c_4])).

tff(c_1838,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2270,plain,(
    ! [D_356] :
      ( ~ r2_hidden('#skF_3',D_356)
      | ~ r1_tarski(D_356,'#skF_4')
      | ~ v3_pre_topc(D_356,'#skF_2')
      | ~ m1_subset_1(D_356,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1838,c_38])).

tff(c_2278,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',A_6)
      | ~ r1_tarski(A_6,'#skF_4')
      | ~ v3_pre_topc(A_6,'#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2270])).

tff(c_2362,plain,(
    ! [A_371] :
      ( ~ r2_hidden('#skF_3',A_371)
      | ~ v3_pre_topc(A_371,'#skF_2')
      | ~ r1_tarski(A_371,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2354,c_2278])).

tff(c_2366,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2265,c_2362])).

tff(c_2375,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2366])).

tff(c_2562,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2558,c_2375])).

tff(c_2575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1837,c_1844,c_2257,c_2562])).

tff(c_2576,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2581,plain,(
    ! [A_404,B_405] :
      ( r1_tarski(A_404,B_405)
      | ~ m1_subset_1(A_404,k1_zfmisc_1(B_405)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2589,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_2581])).

tff(c_2612,plain,(
    ! [A_417,B_418] :
      ( r1_tarski(k1_tops_1(A_417,B_418),B_418)
      | ~ m1_subset_1(B_418,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ l1_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2617,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2612])).

tff(c_2621,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2617])).

tff(c_3071,plain,(
    ! [B_490,A_491,C_492] :
      ( r2_hidden(B_490,k1_tops_1(A_491,C_492))
      | ~ m1_connsp_2(C_492,A_491,B_490)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ m1_subset_1(B_490,u1_struct_0(A_491))
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3076,plain,(
    ! [B_490] :
      ( r2_hidden(B_490,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_490)
      | ~ m1_subset_1(B_490,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_3071])).

tff(c_3080,plain,(
    ! [B_490] :
      ( r2_hidden(B_490,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_490)
      | ~ m1_subset_1(B_490,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3076])).

tff(c_3082,plain,(
    ! [B_493] :
      ( r2_hidden(B_493,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_493)
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3080])).

tff(c_2622,plain,(
    ! [A_419,B_420] :
      ( v3_pre_topc(k1_tops_1(A_419,B_420),A_419)
      | ~ m1_subset_1(B_420,k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2628,plain,(
    ! [A_419,A_6] :
      ( v3_pre_topc(k1_tops_1(A_419,A_6),A_419)
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | ~ r1_tarski(A_6,u1_struct_0(A_419)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2622])).

tff(c_2599,plain,(
    ! [C_411,B_412,A_413] :
      ( r2_hidden(C_411,B_412)
      | ~ r2_hidden(C_411,A_413)
      | ~ r1_tarski(A_413,B_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2603,plain,(
    ! [A_414,B_415,B_416] :
      ( r2_hidden('#skF_1'(A_414,B_415),B_416)
      | ~ r1_tarski(A_414,B_416)
      | r1_tarski(A_414,B_415) ) ),
    inference(resolution,[status(thm)],[c_6,c_2599])).

tff(c_2666,plain,(
    ! [A_427,B_428,B_429,B_430] :
      ( r2_hidden('#skF_1'(A_427,B_428),B_429)
      | ~ r1_tarski(B_430,B_429)
      | ~ r1_tarski(A_427,B_430)
      | r1_tarski(A_427,B_428) ) ),
    inference(resolution,[status(thm)],[c_2603,c_2])).

tff(c_2679,plain,(
    ! [A_431,B_432] :
      ( r2_hidden('#skF_1'(A_431,B_432),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_431,'#skF_4')
      | r1_tarski(A_431,B_432) ) ),
    inference(resolution,[status(thm)],[c_2589,c_2666])).

tff(c_2688,plain,(
    ! [A_433] :
      ( ~ r1_tarski(A_433,'#skF_4')
      | r1_tarski(A_433,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2679,c_4])).

tff(c_2577,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2635,plain,(
    ! [D_425] :
      ( ~ r2_hidden('#skF_3',D_425)
      | ~ r1_tarski(D_425,'#skF_4')
      | ~ v3_pre_topc(D_425,'#skF_2')
      | ~ m1_subset_1(D_425,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2577,c_46])).

tff(c_2643,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',A_6)
      | ~ r1_tarski(A_6,'#skF_4')
      | ~ v3_pre_topc(A_6,'#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2635])).

tff(c_2696,plain,(
    ! [A_434] :
      ( ~ r2_hidden('#skF_3',A_434)
      | ~ v3_pre_topc(A_434,'#skF_2')
      | ~ r1_tarski(A_434,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2688,c_2643])).

tff(c_2700,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2628,c_2696])).

tff(c_2706,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',A_6))
      | ~ r1_tarski(k1_tops_1('#skF_2',A_6),'#skF_4')
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2700])).

tff(c_3088,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3082,c_2706])).

tff(c_3105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2576,c_2589,c_2621,c_3088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.03  
% 5.37/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.37/2.04  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.37/2.04  
% 5.37/2.04  %Foreground sorts:
% 5.37/2.04  
% 5.37/2.04  
% 5.37/2.04  %Background operators:
% 5.37/2.04  
% 5.37/2.04  
% 5.37/2.04  %Foreground operators:
% 5.37/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.37/2.04  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.37/2.04  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.37/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.37/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.37/2.04  tff('#skF_2', type, '#skF_2': $i).
% 5.37/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.37/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.37/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.37/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.37/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.37/2.04  
% 5.69/2.07  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.69/2.07  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.69/2.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.69/2.07  tff(f_44, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.69/2.07  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.69/2.07  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.69/2.07  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 5.69/2.07  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.69/2.07  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_55, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 5.69/2.07  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_56, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_60, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 5.69/2.07  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1296, plain, (![C_181, B_182, A_183]: (r2_hidden(C_181, B_182) | ~r2_hidden(C_181, A_183) | ~r1_tarski(A_183, B_182))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1377, plain, (![A_195, B_196, B_197]: (r2_hidden('#skF_1'(A_195, B_196), B_197) | ~r1_tarski(A_195, B_197) | r1_tarski(A_195, B_196))), inference(resolution, [status(thm)], [c_6, c_1296])).
% 5.69/2.07  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1398, plain, (![A_202, B_203, B_204, B_205]: (r2_hidden('#skF_1'(A_202, B_203), B_204) | ~r1_tarski(B_205, B_204) | ~r1_tarski(A_202, B_205) | r1_tarski(A_202, B_203))), inference(resolution, [status(thm)], [c_1377, c_2])).
% 5.69/2.07  tff(c_1461, plain, (![A_211, B_212]: (r2_hidden('#skF_1'(A_211, B_212), u1_struct_0('#skF_2')) | ~r1_tarski(A_211, '#skF_4') | r1_tarski(A_211, B_212))), inference(resolution, [status(thm)], [c_60, c_1398])).
% 5.69/2.07  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1470, plain, (![A_213]: (~r1_tarski(A_213, '#skF_4') | r1_tarski(A_213, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1461, c_4])).
% 5.69/2.07  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_53, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 5.69/2.07  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 5.69/2.07  tff(c_52, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 5.69/2.07  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_34, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_268, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 5.69/2.07  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_184, plain, (![A_76, B_77]: (v3_pre_topc(k1_tops_1(A_76, B_77), A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.69/2.07  tff(c_191, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_184])).
% 5.69/2.07  tff(c_198, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_191])).
% 5.69/2.07  tff(c_67, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), A_59) | r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_72, plain, (![A_59]: (r1_tarski(A_59, A_59))), inference(resolution, [status(thm)], [c_67, c_4])).
% 5.69/2.07  tff(c_113, plain, (![A_68, B_69]: (r1_tarski(k1_tops_1(A_68, B_69), B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.07  tff(c_120, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_113])).
% 5.69/2.07  tff(c_127, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_120])).
% 5.69/2.07  tff(c_80, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_199, plain, (![A_78, B_79, B_80]: (r2_hidden('#skF_1'(A_78, B_79), B_80) | ~r1_tarski(A_78, B_80) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_6, c_80])).
% 5.69/2.07  tff(c_210, plain, (![A_83, B_84, B_85, B_86]: (r2_hidden('#skF_1'(A_83, B_84), B_85) | ~r1_tarski(B_86, B_85) | ~r1_tarski(A_83, B_86) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_199, c_2])).
% 5.69/2.07  tff(c_281, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), u1_struct_0('#skF_2')) | ~r1_tarski(A_91, '#skF_4') | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_60, c_210])).
% 5.69/2.07  tff(c_291, plain, (![A_93]: (~r1_tarski(A_93, '#skF_4') | r1_tarski(A_93, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_281, c_4])).
% 5.69/2.07  tff(c_206, plain, (![A_78, B_79, B_2, B_80]: (r2_hidden('#skF_1'(A_78, B_79), B_2) | ~r1_tarski(B_80, B_2) | ~r1_tarski(A_78, B_80) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_199, c_2])).
% 5.69/2.07  tff(c_833, plain, (![A_157, B_158, A_159]: (r2_hidden('#skF_1'(A_157, B_158), u1_struct_0('#skF_2')) | ~r1_tarski(A_157, A_159) | r1_tarski(A_157, B_158) | ~r1_tarski(A_159, '#skF_4'))), inference(resolution, [status(thm)], [c_291, c_206])).
% 5.69/2.07  tff(c_857, plain, (![B_158]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_4'), B_158), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_158) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_127, c_833])).
% 5.69/2.07  tff(c_943, plain, (![B_164]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_4'), B_164), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_164))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_857])).
% 5.69/2.07  tff(c_951, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_943, c_4])).
% 5.69/2.07  tff(c_734, plain, (![B_146, A_147, C_148]: (m1_connsp_2(B_146, A_147, C_148) | ~r2_hidden(C_148, B_146) | ~v3_pre_topc(B_146, A_147) | ~m1_subset_1(C_148, u1_struct_0(A_147)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.69/2.07  tff(c_736, plain, (![B_146]: (m1_connsp_2(B_146, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_146) | ~v3_pre_topc(B_146, '#skF_2') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_734])).
% 5.69/2.07  tff(c_739, plain, (![B_146]: (m1_connsp_2(B_146, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_146) | ~v3_pre_topc(B_146, '#skF_2') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_736])).
% 5.69/2.07  tff(c_741, plain, (![B_149]: (m1_connsp_2(B_149, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_149) | ~v3_pre_topc(B_149, '#skF_2') | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_739])).
% 5.69/2.07  tff(c_755, plain, (![A_6]: (m1_connsp_2(A_6, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', A_6) | ~v3_pre_topc(A_6, '#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_741])).
% 5.69/2.07  tff(c_956, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_951, c_755])).
% 5.69/2.07  tff(c_968, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_956])).
% 5.69/2.07  tff(c_975, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_968])).
% 5.69/2.07  tff(c_16, plain, (![A_13, B_17, C_19]: (r1_tarski(k1_tops_1(A_13, B_17), k1_tops_1(A_13, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.69/2.07  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_78, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_74, c_8])).
% 5.69/2.07  tff(c_744, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_741])).
% 5.69/2.07  tff(c_754, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_54, c_744])).
% 5.69/2.07  tff(c_476, plain, (![B_114, A_115, C_116]: (r2_hidden(B_114, k1_tops_1(A_115, C_116)) | ~m1_connsp_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_114, u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.69/2.07  tff(c_488, plain, (![B_114, A_115, A_6]: (r2_hidden(B_114, k1_tops_1(A_115, A_6)) | ~m1_connsp_2(A_6, A_115, B_114) | ~m1_subset_1(B_114, u1_struct_0(A_115)) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | ~r1_tarski(A_6, u1_struct_0(A_115)))), inference(resolution, [status(thm)], [c_10, c_476])).
% 5.69/2.07  tff(c_186, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_74, c_184])).
% 5.69/2.07  tff(c_194, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_186])).
% 5.69/2.07  tff(c_115, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_74, c_113])).
% 5.69/2.07  tff(c_123, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_115])).
% 5.69/2.07  tff(c_855, plain, (![B_158]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_5'), B_158), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_158) | ~r1_tarski('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_123, c_833])).
% 5.69/2.07  tff(c_1082, plain, (![B_175]: (r2_hidden('#skF_1'(k1_tops_1('#skF_2', '#skF_5'), B_175), u1_struct_0('#skF_2')) | r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_175))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_855])).
% 5.69/2.07  tff(c_1090, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1082, c_4])).
% 5.69/2.07  tff(c_1097, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_5'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_1090, c_755])).
% 5.69/2.07  tff(c_1108, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_5'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_1097])).
% 5.69/2.07  tff(c_1114, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1108])).
% 5.69/2.07  tff(c_1137, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_488, c_1114])).
% 5.69/2.07  tff(c_1149, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_30, c_28, c_26, c_754, c_1137])).
% 5.69/2.07  tff(c_1151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1149])).
% 5.69/2.07  tff(c_1153, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(splitRight, [status(thm)], [c_1108])).
% 5.69/2.07  tff(c_1163, plain, (![B_178]: (r2_hidden('#skF_3', B_178) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_178))), inference(resolution, [status(thm)], [c_1153, c_2])).
% 5.69/2.07  tff(c_1182, plain, (![C_19]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_19)) | ~r1_tarski('#skF_5', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_1163])).
% 5.69/2.07  tff(c_1241, plain, (![C_179]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_179)) | ~r1_tarski('#skF_5', C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_74, c_1182])).
% 5.69/2.07  tff(c_1251, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_1241])).
% 5.69/2.07  tff(c_1258, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1251])).
% 5.69/2.07  tff(c_1260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_975, c_1258])).
% 5.69/2.07  tff(c_1262, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_968])).
% 5.69/2.07  tff(c_18, plain, (![C_26, A_20, B_24]: (m1_connsp_2(C_26, A_20, B_24) | ~r2_hidden(B_24, k1_tops_1(A_20, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.69/2.07  tff(c_1264, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1262, c_18])).
% 5.69/2.07  tff(c_1269, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_1264])).
% 5.69/2.07  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_268, c_1269])).
% 5.69/2.07  tff(c_1274, plain, (![D_180]: (~r2_hidden('#skF_3', D_180) | ~r1_tarski(D_180, '#skF_4') | ~v3_pre_topc(D_180, '#skF_2') | ~m1_subset_1(D_180, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_34])).
% 5.69/2.07  tff(c_1277, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_1274])).
% 5.69/2.07  tff(c_1288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_1277])).
% 5.69/2.07  tff(c_1290, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 5.69/2.07  tff(c_1294, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_1290])).
% 5.69/2.07  tff(c_1483, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1470, c_1294])).
% 5.69/2.07  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_1483])).
% 5.69/2.07  tff(c_1495, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.69/2.07  tff(c_1498, plain, (![A_216, B_217]: (r1_tarski(A_216, B_217) | ~m1_subset_1(A_216, k1_zfmisc_1(B_217)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_1506, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1498])).
% 5.69/2.07  tff(c_1523, plain, (![A_226, B_227]: (r1_tarski(k1_tops_1(A_226, B_227), B_227) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.07  tff(c_1528, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1523])).
% 5.69/2.07  tff(c_1532, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1528])).
% 5.69/2.07  tff(c_1808, plain, (![B_272, A_273, C_274]: (r2_hidden(B_272, k1_tops_1(A_273, C_274)) | ~m1_connsp_2(C_274, A_273, B_272) | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(B_272, u1_struct_0(A_273)) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.69/2.07  tff(c_1813, plain, (![B_272]: (r2_hidden(B_272, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_272) | ~m1_subset_1(B_272, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1808])).
% 5.69/2.07  tff(c_1817, plain, (![B_272]: (r2_hidden(B_272, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_272) | ~m1_subset_1(B_272, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1813])).
% 5.69/2.07  tff(c_1819, plain, (![B_275]: (r2_hidden(B_275, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_275) | ~m1_subset_1(B_275, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1817])).
% 5.69/2.07  tff(c_1562, plain, (![A_236, B_237]: (v3_pre_topc(k1_tops_1(A_236, B_237), A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.69/2.07  tff(c_1568, plain, (![A_236, A_6]: (v3_pre_topc(k1_tops_1(A_236, A_6), A_236) | ~l1_pre_topc(A_236) | ~v2_pre_topc(A_236) | ~r1_tarski(A_6, u1_struct_0(A_236)))), inference(resolution, [status(thm)], [c_10, c_1562])).
% 5.69/2.07  tff(c_1516, plain, (![C_223, B_224, A_225]: (r2_hidden(C_223, B_224) | ~r2_hidden(C_223, A_225) | ~r1_tarski(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1549, plain, (![A_231, B_232, B_233]: (r2_hidden('#skF_1'(A_231, B_232), B_233) | ~r1_tarski(A_231, B_233) | r1_tarski(A_231, B_232))), inference(resolution, [status(thm)], [c_6, c_1516])).
% 5.69/2.07  tff(c_1574, plain, (![A_240, B_241, B_242, B_243]: (r2_hidden('#skF_1'(A_240, B_241), B_242) | ~r1_tarski(B_243, B_242) | ~r1_tarski(A_240, B_243) | r1_tarski(A_240, B_241))), inference(resolution, [status(thm)], [c_1549, c_2])).
% 5.69/2.07  tff(c_1601, plain, (![A_245, B_246]: (r2_hidden('#skF_1'(A_245, B_246), u1_struct_0('#skF_2')) | ~r1_tarski(A_245, '#skF_4') | r1_tarski(A_245, B_246))), inference(resolution, [status(thm)], [c_1506, c_1574])).
% 5.69/2.07  tff(c_1609, plain, (![A_245]: (~r1_tarski(A_245, '#skF_4') | r1_tarski(A_245, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1601, c_4])).
% 5.69/2.07  tff(c_1496, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 5.69/2.07  tff(c_42, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_1588, plain, (![D_244]: (~r2_hidden('#skF_3', D_244) | ~r1_tarski(D_244, '#skF_4') | ~v3_pre_topc(D_244, '#skF_2') | ~m1_subset_1(D_244, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1496, c_42])).
% 5.69/2.07  tff(c_1629, plain, (![A_249]: (~r2_hidden('#skF_3', A_249) | ~r1_tarski(A_249, '#skF_4') | ~v3_pre_topc(A_249, '#skF_2') | ~r1_tarski(A_249, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_1588])).
% 5.69/2.07  tff(c_1650, plain, (![A_250]: (~r2_hidden('#skF_3', A_250) | ~v3_pre_topc(A_250, '#skF_2') | ~r1_tarski(A_250, '#skF_4'))), inference(resolution, [status(thm)], [c_1609, c_1629])).
% 5.69/2.07  tff(c_1654, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1568, c_1650])).
% 5.69/2.07  tff(c_1663, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1654])).
% 5.69/2.07  tff(c_1823, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1819, c_1663])).
% 5.69/2.07  tff(c_1836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1495, c_1506, c_1532, c_1823])).
% 5.69/2.07  tff(c_1837, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 5.69/2.07  tff(c_1840, plain, (![A_276, B_277]: (r1_tarski(A_276, B_277) | ~m1_subset_1(A_276, k1_zfmisc_1(B_277)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_1844, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1840])).
% 5.69/2.07  tff(c_2248, plain, (![A_350, B_351]: (r1_tarski(k1_tops_1(A_350, B_351), B_351) | ~m1_subset_1(B_351, k1_zfmisc_1(u1_struct_0(A_350))) | ~l1_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.07  tff(c_2253, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2248])).
% 5.69/2.07  tff(c_2257, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2253])).
% 5.69/2.07  tff(c_2523, plain, (![B_395, A_396, C_397]: (r2_hidden(B_395, k1_tops_1(A_396, C_397)) | ~m1_connsp_2(C_397, A_396, B_395) | ~m1_subset_1(C_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~m1_subset_1(B_395, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.69/2.07  tff(c_2528, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2523])).
% 5.69/2.07  tff(c_2532, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2528])).
% 5.69/2.07  tff(c_2558, plain, (![B_401]: (r2_hidden(B_401, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_401) | ~m1_subset_1(B_401, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2532])).
% 5.69/2.07  tff(c_2259, plain, (![A_354, B_355]: (v3_pre_topc(k1_tops_1(A_354, B_355), A_354) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.69/2.07  tff(c_2265, plain, (![A_354, A_6]: (v3_pre_topc(k1_tops_1(A_354, A_6), A_354) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | ~r1_tarski(A_6, u1_struct_0(A_354)))), inference(resolution, [status(thm)], [c_10, c_2259])).
% 5.69/2.07  tff(c_1857, plain, (![C_284, B_285, A_286]: (r2_hidden(C_284, B_285) | ~r2_hidden(C_284, A_286) | ~r1_tarski(A_286, B_285))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_1863, plain, (![A_288, B_289, B_290]: (r2_hidden('#skF_1'(A_288, B_289), B_290) | ~r1_tarski(A_288, B_290) | r1_tarski(A_288, B_289))), inference(resolution, [status(thm)], [c_6, c_1857])).
% 5.69/2.07  tff(c_2304, plain, (![A_360, B_361, B_362, B_363]: (r2_hidden('#skF_1'(A_360, B_361), B_362) | ~r1_tarski(B_363, B_362) | ~r1_tarski(A_360, B_363) | r1_tarski(A_360, B_361))), inference(resolution, [status(thm)], [c_1863, c_2])).
% 5.69/2.07  tff(c_2345, plain, (![A_368, B_369]: (r2_hidden('#skF_1'(A_368, B_369), u1_struct_0('#skF_2')) | ~r1_tarski(A_368, '#skF_4') | r1_tarski(A_368, B_369))), inference(resolution, [status(thm)], [c_1844, c_2304])).
% 5.69/2.07  tff(c_2354, plain, (![A_370]: (~r1_tarski(A_370, '#skF_4') | r1_tarski(A_370, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2345, c_4])).
% 5.69/2.07  tff(c_1838, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 5.69/2.07  tff(c_38, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_2270, plain, (![D_356]: (~r2_hidden('#skF_3', D_356) | ~r1_tarski(D_356, '#skF_4') | ~v3_pre_topc(D_356, '#skF_2') | ~m1_subset_1(D_356, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1838, c_38])).
% 5.69/2.07  tff(c_2278, plain, (![A_6]: (~r2_hidden('#skF_3', A_6) | ~r1_tarski(A_6, '#skF_4') | ~v3_pre_topc(A_6, '#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_2270])).
% 5.69/2.07  tff(c_2362, plain, (![A_371]: (~r2_hidden('#skF_3', A_371) | ~v3_pre_topc(A_371, '#skF_2') | ~r1_tarski(A_371, '#skF_4'))), inference(resolution, [status(thm)], [c_2354, c_2278])).
% 5.69/2.07  tff(c_2366, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2265, c_2362])).
% 5.69/2.07  tff(c_2375, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2366])).
% 5.69/2.07  tff(c_2562, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2558, c_2375])).
% 5.69/2.07  tff(c_2575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1837, c_1844, c_2257, c_2562])).
% 5.69/2.07  tff(c_2576, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 5.69/2.07  tff(c_2581, plain, (![A_404, B_405]: (r1_tarski(A_404, B_405) | ~m1_subset_1(A_404, k1_zfmisc_1(B_405)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.07  tff(c_2589, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2581])).
% 5.69/2.07  tff(c_2612, plain, (![A_417, B_418]: (r1_tarski(k1_tops_1(A_417, B_418), B_418) | ~m1_subset_1(B_418, k1_zfmisc_1(u1_struct_0(A_417))) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.07  tff(c_2617, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2612])).
% 5.69/2.07  tff(c_2621, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2617])).
% 5.69/2.07  tff(c_3071, plain, (![B_490, A_491, C_492]: (r2_hidden(B_490, k1_tops_1(A_491, C_492)) | ~m1_connsp_2(C_492, A_491, B_490) | ~m1_subset_1(C_492, k1_zfmisc_1(u1_struct_0(A_491))) | ~m1_subset_1(B_490, u1_struct_0(A_491)) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.69/2.07  tff(c_3076, plain, (![B_490]: (r2_hidden(B_490, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_490) | ~m1_subset_1(B_490, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_3071])).
% 5.69/2.07  tff(c_3080, plain, (![B_490]: (r2_hidden(B_490, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_490) | ~m1_subset_1(B_490, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3076])).
% 5.69/2.07  tff(c_3082, plain, (![B_493]: (r2_hidden(B_493, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_493) | ~m1_subset_1(B_493, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_3080])).
% 5.69/2.07  tff(c_2622, plain, (![A_419, B_420]: (v3_pre_topc(k1_tops_1(A_419, B_420), A_419) | ~m1_subset_1(B_420, k1_zfmisc_1(u1_struct_0(A_419))) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.69/2.07  tff(c_2628, plain, (![A_419, A_6]: (v3_pre_topc(k1_tops_1(A_419, A_6), A_419) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419) | ~r1_tarski(A_6, u1_struct_0(A_419)))), inference(resolution, [status(thm)], [c_10, c_2622])).
% 5.69/2.07  tff(c_2599, plain, (![C_411, B_412, A_413]: (r2_hidden(C_411, B_412) | ~r2_hidden(C_411, A_413) | ~r1_tarski(A_413, B_412))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.07  tff(c_2603, plain, (![A_414, B_415, B_416]: (r2_hidden('#skF_1'(A_414, B_415), B_416) | ~r1_tarski(A_414, B_416) | r1_tarski(A_414, B_415))), inference(resolution, [status(thm)], [c_6, c_2599])).
% 5.69/2.07  tff(c_2666, plain, (![A_427, B_428, B_429, B_430]: (r2_hidden('#skF_1'(A_427, B_428), B_429) | ~r1_tarski(B_430, B_429) | ~r1_tarski(A_427, B_430) | r1_tarski(A_427, B_428))), inference(resolution, [status(thm)], [c_2603, c_2])).
% 5.69/2.07  tff(c_2679, plain, (![A_431, B_432]: (r2_hidden('#skF_1'(A_431, B_432), u1_struct_0('#skF_2')) | ~r1_tarski(A_431, '#skF_4') | r1_tarski(A_431, B_432))), inference(resolution, [status(thm)], [c_2589, c_2666])).
% 5.69/2.07  tff(c_2688, plain, (![A_433]: (~r1_tarski(A_433, '#skF_4') | r1_tarski(A_433, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2679, c_4])).
% 5.69/2.07  tff(c_2577, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.69/2.07  tff(c_46, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.69/2.07  tff(c_2635, plain, (![D_425]: (~r2_hidden('#skF_3', D_425) | ~r1_tarski(D_425, '#skF_4') | ~v3_pre_topc(D_425, '#skF_2') | ~m1_subset_1(D_425, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2577, c_46])).
% 5.69/2.07  tff(c_2643, plain, (![A_6]: (~r2_hidden('#skF_3', A_6) | ~r1_tarski(A_6, '#skF_4') | ~v3_pre_topc(A_6, '#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_2635])).
% 5.69/2.07  tff(c_2696, plain, (![A_434]: (~r2_hidden('#skF_3', A_434) | ~v3_pre_topc(A_434, '#skF_2') | ~r1_tarski(A_434, '#skF_4'))), inference(resolution, [status(thm)], [c_2688, c_2643])).
% 5.69/2.07  tff(c_2700, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2628, c_2696])).
% 5.69/2.07  tff(c_2706, plain, (![A_6]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', A_6)) | ~r1_tarski(k1_tops_1('#skF_2', A_6), '#skF_4') | ~r1_tarski(A_6, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2700])).
% 5.69/2.07  tff(c_3088, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2')) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3082, c_2706])).
% 5.69/2.07  tff(c_3105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2576, c_2589, c_2621, c_3088])).
% 5.69/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.07  
% 5.69/2.07  Inference rules
% 5.69/2.07  ----------------------
% 5.69/2.07  #Ref     : 0
% 5.69/2.07  #Sup     : 640
% 5.69/2.07  #Fact    : 0
% 5.69/2.07  #Define  : 0
% 5.69/2.07  #Split   : 22
% 5.69/2.07  #Chain   : 0
% 5.69/2.07  #Close   : 0
% 5.69/2.07  
% 5.69/2.07  Ordering : KBO
% 5.69/2.07  
% 5.69/2.07  Simplification rules
% 5.69/2.07  ----------------------
% 5.69/2.07  #Subsume      : 151
% 5.69/2.07  #Demod        : 337
% 5.85/2.07  #Tautology    : 115
% 5.85/2.07  #SimpNegUnit  : 23
% 5.85/2.07  #BackRed      : 0
% 5.85/2.07  
% 5.85/2.07  #Partial instantiations: 0
% 5.85/2.07  #Strategies tried      : 1
% 5.85/2.07  
% 5.85/2.07  Timing (in seconds)
% 5.85/2.07  ----------------------
% 5.85/2.08  Preprocessing        : 0.32
% 5.85/2.08  Parsing              : 0.17
% 5.85/2.08  CNF conversion       : 0.03
% 5.85/2.08  Main loop            : 0.94
% 5.85/2.08  Inferencing          : 0.35
% 5.85/2.08  Reduction            : 0.26
% 5.85/2.08  Demodulation         : 0.17
% 5.85/2.08  BG Simplification    : 0.03
% 5.85/2.08  Subsumption          : 0.23
% 5.85/2.08  Abstraction          : 0.03
% 5.85/2.08  MUC search           : 0.00
% 5.85/2.08  Cooper               : 0.00
% 5.85/2.08  Total                : 1.34
% 5.85/2.08  Index Insertion      : 0.00
% 5.85/2.08  Index Deletion       : 0.00
% 5.85/2.08  Index Matching       : 0.00
% 5.85/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
