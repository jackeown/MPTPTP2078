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
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 293 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  223 (1151 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
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

tff(f_133,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_116,axiom,(
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

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1515,plain,(
    ! [B_245,A_246,C_247] :
      ( r2_hidden(B_245,k1_tops_1(A_246,C_247))
      | ~ m1_connsp_2(C_247,A_246,B_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(B_245,u1_struct_0(A_246))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1525,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1515])).

tff(c_1531,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1525])).

tff(c_1532,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_245)
      | ~ m1_subset_1(B_245,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1531])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1551,plain,(
    ! [B_249] :
      ( r2_hidden(B_249,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_249)
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1531])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [C_83,B_84,A_85] :
      ( ~ v1_xboole_0(C_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(C_83))
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,(
    ! [B_13,A_85,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_85,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_103])).

tff(c_1581,plain,(
    ! [B_13,B_249] :
      ( ~ v1_xboole_0(B_13)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_13)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_249)
      | ~ m1_subset_1(B_249,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1551,c_108])).

tff(c_1603,plain,(
    ! [B_252] :
      ( ~ m1_connsp_2('#skF_5','#skF_3',B_252)
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_1581])).

tff(c_1616,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1603])).

tff(c_1623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1616])).

tff(c_1625,plain,(
    ! [B_253] :
      ( ~ v1_xboole_0(B_253)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_253) ) ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_1660,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_1625])).

tff(c_215,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k1_tops_1(A_121,B_122),B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_223,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_215])).

tff(c_228,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_223])).

tff(c_229,plain,(
    ! [A_123,B_124] :
      ( v3_pre_topc(k1_tops_1(A_123,B_124),A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_237,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_229])).

tff(c_242,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_237])).

tff(c_61,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [A_111,B_112,B_113] :
      ( r2_hidden('#skF_1'(A_111,B_112),B_113)
      | ~ r1_tarski(A_111,B_113)
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_706,plain,(
    ! [A_184,B_185,B_186,B_187] :
      ( r2_hidden('#skF_1'(A_184,B_185),B_186)
      | ~ r1_tarski(B_187,B_186)
      | ~ r1_tarski(A_184,B_187)
      | r1_tarski(A_184,B_185) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_734,plain,(
    ! [A_188,B_189] :
      ( r2_hidden('#skF_1'(A_188,B_189),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_188,'#skF_5')
      | r1_tarski(A_188,B_189) ) ),
    inference(resolution,[status(thm)],[c_65,c_706])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_760,plain,(
    ! [A_188] :
      ( ~ r1_tarski(A_188,'#skF_5')
      | r1_tarski(A_188,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_734,c_4])).

tff(c_40,plain,(
    ! [B_45,D_51,C_49,A_37] :
      ( k1_tops_1(B_45,D_51) = D_51
      | ~ v3_pre_topc(D_51,B_45)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0(B_45)))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(B_45)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_992,plain,(
    ! [C_202,A_203] :
      ( ~ m1_subset_1(C_202,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203) ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_1003,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_992])).

tff(c_1009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1003])).

tff(c_1011,plain,(
    ! [B_204,D_205] :
      ( k1_tops_1(B_204,D_205) = D_205
      | ~ v3_pre_topc(D_205,B_204)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0(B_204)))
      | ~ l1_pre_topc(B_204) ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1032,plain,(
    ! [B_206,A_207] :
      ( k1_tops_1(B_206,A_207) = A_207
      | ~ v3_pre_topc(A_207,B_206)
      | ~ l1_pre_topc(B_206)
      | ~ r1_tarski(A_207,u1_struct_0(B_206)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1011])).

tff(c_1035,plain,(
    ! [A_188] :
      ( k1_tops_1('#skF_3',A_188) = A_188
      | ~ v3_pre_topc(A_188,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_188,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_760,c_1032])).

tff(c_1080,plain,(
    ! [A_208] :
      ( k1_tops_1('#skF_3',A_208) = A_208
      | ~ v3_pre_topc(A_208,'#skF_3')
      | ~ r1_tarski(A_208,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1035])).

tff(c_1090,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_242,c_1080])).

tff(c_1097,plain,(
    k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1090])).

tff(c_1684,plain,(
    ! [C_255,A_256,B_257] :
      ( m1_connsp_2(C_255,A_256,B_257)
      | ~ r2_hidden(B_257,k1_tops_1(A_256,C_255))
      | ~ m1_subset_1(C_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(B_257,u1_struct_0(A_256))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1688,plain,(
    ! [B_257] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_257)
      | ~ r2_hidden(B_257,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_1684])).

tff(c_1703,plain,(
    ! [B_257] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_257)
      | ~ r2_hidden(B_257,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1688])).

tff(c_1704,plain,(
    ! [B_257] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_257)
      | ~ r2_hidden(B_257,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1703])).

tff(c_1773,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1704])).

tff(c_1777,plain,(
    ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1773])).

tff(c_1780,plain,(
    ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_760,c_1777])).

tff(c_1790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_1780])).

tff(c_2426,plain,(
    ! [B_309] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_309)
      | ~ r2_hidden(B_309,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_1704])).

tff(c_761,plain,(
    ! [A_190] :
      ( ~ r1_tarski(A_190,'#skF_5')
      | r1_tarski(A_190,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_734,c_4])).

tff(c_74,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(A_75,k1_zfmisc_1(B_76))
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [D_70] :
      ( ~ r1_tarski(D_70,'#skF_5')
      | ~ v3_pre_topc(D_70,'#skF_3')
      | ~ m1_connsp_2(D_70,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_82,plain,(
    ! [A_75] :
      ( ~ r1_tarski(A_75,'#skF_5')
      | ~ v3_pre_topc(A_75,'#skF_3')
      | ~ m1_connsp_2(A_75,'#skF_3','#skF_4')
      | v1_xboole_0(A_75)
      | ~ r1_tarski(A_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_46])).

tff(c_783,plain,(
    ! [A_190] :
      ( ~ v3_pre_topc(A_190,'#skF_3')
      | ~ m1_connsp_2(A_190,'#skF_3','#skF_4')
      | v1_xboole_0(A_190)
      | ~ r1_tarski(A_190,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_761,c_82])).

tff(c_2433,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2426,c_783])).

tff(c_2437,plain,
    ( v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_228,c_242,c_2433])).

tff(c_2438,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1660,c_2437])).

tff(c_2441,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1532,c_2438])).

tff(c_2445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.95  
% 5.09/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.96  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.09/1.96  
% 5.09/1.96  %Foreground sorts:
% 5.09/1.96  
% 5.09/1.96  
% 5.09/1.96  %Background operators:
% 5.09/1.96  
% 5.09/1.96  
% 5.09/1.96  %Foreground operators:
% 5.09/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.09/1.96  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.09/1.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.09/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.09/1.96  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.09/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.09/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.09/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.09/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.09/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.09/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.09/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/1.96  
% 5.09/1.98  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 5.09/1.98  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.09/1.98  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.09/1.98  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.09/1.98  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.09/1.98  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.09/1.98  tff(f_70, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.09/1.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.09/1.98  tff(f_116, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 5.09/1.98  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_48, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_1515, plain, (![B_245, A_246, C_247]: (r2_hidden(B_245, k1_tops_1(A_246, C_247)) | ~m1_connsp_2(C_247, A_246, B_245) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(B_245, u1_struct_0(A_246)) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.09/1.98  tff(c_1525, plain, (![B_245]: (r2_hidden(B_245, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_1515])).
% 5.09/1.98  tff(c_1531, plain, (![B_245]: (r2_hidden(B_245, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1525])).
% 5.09/1.98  tff(c_1532, plain, (![B_245]: (r2_hidden(B_245, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_245) | ~m1_subset_1(B_245, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1531])).
% 5.09/1.98  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.09/1.98  tff(c_1551, plain, (![B_249]: (r2_hidden(B_249, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_249) | ~m1_subset_1(B_249, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1531])).
% 5.09/1.98  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.98  tff(c_103, plain, (![C_83, B_84, A_85]: (~v1_xboole_0(C_83) | ~m1_subset_1(B_84, k1_zfmisc_1(C_83)) | ~r2_hidden(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.09/1.98  tff(c_108, plain, (![B_13, A_85, A_12]: (~v1_xboole_0(B_13) | ~r2_hidden(A_85, A_12) | ~r1_tarski(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_103])).
% 5.09/1.98  tff(c_1581, plain, (![B_13, B_249]: (~v1_xboole_0(B_13) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_13) | ~m1_connsp_2('#skF_5', '#skF_3', B_249) | ~m1_subset_1(B_249, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1551, c_108])).
% 5.09/1.98  tff(c_1603, plain, (![B_252]: (~m1_connsp_2('#skF_5', '#skF_3', B_252) | ~m1_subset_1(B_252, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1581])).
% 5.09/1.98  tff(c_1616, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1603])).
% 5.09/1.98  tff(c_1623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1616])).
% 5.09/1.98  tff(c_1625, plain, (![B_253]: (~v1_xboole_0(B_253) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_253))), inference(splitRight, [status(thm)], [c_1581])).
% 5.09/1.98  tff(c_1660, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_1625])).
% 5.09/1.98  tff(c_215, plain, (![A_121, B_122]: (r1_tarski(k1_tops_1(A_121, B_122), B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.09/1.98  tff(c_223, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_215])).
% 5.09/1.98  tff(c_228, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_223])).
% 5.09/1.98  tff(c_229, plain, (![A_123, B_124]: (v3_pre_topc(k1_tops_1(A_123, B_124), A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.09/1.98  tff(c_237, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_229])).
% 5.09/1.98  tff(c_242, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_237])).
% 5.09/1.98  tff(c_61, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.98  tff(c_65, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_61])).
% 5.09/1.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.98  tff(c_147, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.98  tff(c_168, plain, (![A_111, B_112, B_113]: (r2_hidden('#skF_1'(A_111, B_112), B_113) | ~r1_tarski(A_111, B_113) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_6, c_147])).
% 5.09/1.98  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.98  tff(c_706, plain, (![A_184, B_185, B_186, B_187]: (r2_hidden('#skF_1'(A_184, B_185), B_186) | ~r1_tarski(B_187, B_186) | ~r1_tarski(A_184, B_187) | r1_tarski(A_184, B_185))), inference(resolution, [status(thm)], [c_168, c_2])).
% 5.09/1.98  tff(c_734, plain, (![A_188, B_189]: (r2_hidden('#skF_1'(A_188, B_189), u1_struct_0('#skF_3')) | ~r1_tarski(A_188, '#skF_5') | r1_tarski(A_188, B_189))), inference(resolution, [status(thm)], [c_65, c_706])).
% 5.09/1.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.98  tff(c_760, plain, (![A_188]: (~r1_tarski(A_188, '#skF_5') | r1_tarski(A_188, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_734, c_4])).
% 5.09/1.98  tff(c_40, plain, (![B_45, D_51, C_49, A_37]: (k1_tops_1(B_45, D_51)=D_51 | ~v3_pre_topc(D_51, B_45) | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0(B_45))) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(B_45) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.09/1.98  tff(c_992, plain, (![C_202, A_203]: (~m1_subset_1(C_202, k1_zfmisc_1(u1_struct_0(A_203))) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203))), inference(splitLeft, [status(thm)], [c_40])).
% 5.09/1.98  tff(c_1003, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_992])).
% 5.09/1.98  tff(c_1009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1003])).
% 5.09/1.98  tff(c_1011, plain, (![B_204, D_205]: (k1_tops_1(B_204, D_205)=D_205 | ~v3_pre_topc(D_205, B_204) | ~m1_subset_1(D_205, k1_zfmisc_1(u1_struct_0(B_204))) | ~l1_pre_topc(B_204))), inference(splitRight, [status(thm)], [c_40])).
% 5.09/1.98  tff(c_1032, plain, (![B_206, A_207]: (k1_tops_1(B_206, A_207)=A_207 | ~v3_pre_topc(A_207, B_206) | ~l1_pre_topc(B_206) | ~r1_tarski(A_207, u1_struct_0(B_206)))), inference(resolution, [status(thm)], [c_18, c_1011])).
% 5.09/1.98  tff(c_1035, plain, (![A_188]: (k1_tops_1('#skF_3', A_188)=A_188 | ~v3_pre_topc(A_188, '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_188, '#skF_5'))), inference(resolution, [status(thm)], [c_760, c_1032])).
% 5.09/1.98  tff(c_1080, plain, (![A_208]: (k1_tops_1('#skF_3', A_208)=A_208 | ~v3_pre_topc(A_208, '#skF_3') | ~r1_tarski(A_208, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1035])).
% 5.09/1.98  tff(c_1090, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_242, c_1080])).
% 5.09/1.98  tff(c_1097, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_1090])).
% 5.09/1.98  tff(c_1684, plain, (![C_255, A_256, B_257]: (m1_connsp_2(C_255, A_256, B_257) | ~r2_hidden(B_257, k1_tops_1(A_256, C_255)) | ~m1_subset_1(C_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(B_257, u1_struct_0(A_256)) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.09/1.98  tff(c_1688, plain, (![B_257]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_257) | ~r2_hidden(B_257, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_257, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1097, c_1684])).
% 5.09/1.98  tff(c_1703, plain, (![B_257]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_257) | ~r2_hidden(B_257, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_257, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1688])).
% 5.09/1.98  tff(c_1704, plain, (![B_257]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_257) | ~r2_hidden(B_257, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_257, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1703])).
% 5.09/1.98  tff(c_1773, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1704])).
% 5.09/1.98  tff(c_1777, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1773])).
% 5.09/1.98  tff(c_1780, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_760, c_1777])).
% 5.09/1.98  tff(c_1790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_1780])).
% 5.09/1.98  tff(c_2426, plain, (![B_309]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_309) | ~r2_hidden(B_309, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(B_309, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1704])).
% 5.09/1.98  tff(c_761, plain, (![A_190]: (~r1_tarski(A_190, '#skF_5') | r1_tarski(A_190, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_734, c_4])).
% 5.09/1.98  tff(c_74, plain, (![A_75, B_76]: (m1_subset_1(A_75, k1_zfmisc_1(B_76)) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.98  tff(c_46, plain, (![D_70]: (~r1_tarski(D_70, '#skF_5') | ~v3_pre_topc(D_70, '#skF_3') | ~m1_connsp_2(D_70, '#skF_3', '#skF_4') | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_70))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.09/1.98  tff(c_82, plain, (![A_75]: (~r1_tarski(A_75, '#skF_5') | ~v3_pre_topc(A_75, '#skF_3') | ~m1_connsp_2(A_75, '#skF_3', '#skF_4') | v1_xboole_0(A_75) | ~r1_tarski(A_75, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_46])).
% 5.09/1.98  tff(c_783, plain, (![A_190]: (~v3_pre_topc(A_190, '#skF_3') | ~m1_connsp_2(A_190, '#skF_3', '#skF_4') | v1_xboole_0(A_190) | ~r1_tarski(A_190, '#skF_5'))), inference(resolution, [status(thm)], [c_761, c_82])).
% 5.09/1.98  tff(c_2433, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2426, c_783])).
% 5.09/1.98  tff(c_2437, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_228, c_242, c_2433])).
% 5.09/1.98  tff(c_2438, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1660, c_2437])).
% 5.09/1.98  tff(c_2441, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1532, c_2438])).
% 5.09/1.98  tff(c_2445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_2441])).
% 5.09/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.98  
% 5.09/1.98  Inference rules
% 5.09/1.98  ----------------------
% 5.09/1.98  #Ref     : 0
% 5.09/1.98  #Sup     : 579
% 5.09/1.98  #Fact    : 0
% 5.09/1.98  #Define  : 0
% 5.09/1.98  #Split   : 12
% 5.09/1.98  #Chain   : 0
% 5.09/1.98  #Close   : 0
% 5.09/1.98  
% 5.09/1.98  Ordering : KBO
% 5.09/1.98  
% 5.09/1.98  Simplification rules
% 5.09/1.98  ----------------------
% 5.09/1.98  #Subsume      : 196
% 5.09/1.98  #Demod        : 118
% 5.09/1.98  #Tautology    : 31
% 5.09/1.98  #SimpNegUnit  : 9
% 5.09/1.98  #BackRed      : 0
% 5.09/1.98  
% 5.09/1.98  #Partial instantiations: 0
% 5.09/1.98  #Strategies tried      : 1
% 5.09/1.98  
% 5.09/1.98  Timing (in seconds)
% 5.09/1.98  ----------------------
% 5.09/1.98  Preprocessing        : 0.33
% 5.09/1.98  Parsing              : 0.18
% 5.09/1.98  CNF conversion       : 0.03
% 5.09/1.98  Main loop            : 0.87
% 5.09/1.98  Inferencing          : 0.26
% 5.09/1.98  Reduction            : 0.21
% 5.09/1.98  Demodulation         : 0.14
% 5.09/1.98  BG Simplification    : 0.03
% 5.09/1.98  Subsumption          : 0.29
% 5.09/1.98  Abstraction          : 0.04
% 5.09/1.98  MUC search           : 0.00
% 5.09/1.98  Cooper               : 0.00
% 5.09/1.98  Total                : 1.24
% 5.09/1.98  Index Insertion      : 0.00
% 5.09/1.98  Index Deletion       : 0.00
% 5.09/1.98  Index Matching       : 0.00
% 5.09/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
