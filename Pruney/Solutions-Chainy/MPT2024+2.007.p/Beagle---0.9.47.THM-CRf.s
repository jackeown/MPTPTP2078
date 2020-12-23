%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 607 expanded)
%              Number of leaves         :   39 ( 246 expanded)
%              Depth                    :   17
%              Number of atoms          :  300 (2288 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_129,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_297,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_connsp_2(C_135,A_136,B_137)
      | ~ m1_subset_1(C_135,u1_struct_0(k9_yellow_6(A_136,B_137)))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_311,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_297])).

tff(c_320,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_311])).

tff(c_321,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_320])).

tff(c_36,plain,(
    ! [C_34,A_31,B_32] :
      ( m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_connsp_2(C_34,A_31,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_329,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_321,c_36])).

tff(c_332,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_329])).

tff(c_333,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_332])).

tff(c_365,plain,(
    ! [C_140,B_141,A_142] :
      ( r2_hidden(C_140,B_141)
      | ~ m1_connsp_2(B_141,A_142,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(A_142))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_367,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_321,c_365])).

tff(c_372,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_333,c_54,c_367])).

tff(c_373,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_372])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,k2_xboole_0(C_86,B_87))
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | ~ r1_tarski(k1_tarski(A_9),B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [A_9,C_86,B_87] :
      ( r2_hidden(A_9,k2_xboole_0(C_86,B_87))
      | ~ r1_tarski(k1_tarski(A_9),B_87) ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_308,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_297])).

tff(c_316,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_308])).

tff(c_317,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_316])).

tff(c_323,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_317,c_36])).

tff(c_326,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_323])).

tff(c_327,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_326])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( k4_subset_1(A_18,B_19,C_20) = k2_xboole_0(B_19,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_447,plain,(
    ! [B_158] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_158,'#skF_5') = k2_xboole_0(B_158,'#skF_5')
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_333,c_26])).

tff(c_467,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_327,c_447])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k4_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_499,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_24])).

tff(c_503,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_333,c_499])).

tff(c_720,plain,(
    ! [C_178,A_179,B_180] :
      ( r2_hidden(C_178,u1_struct_0(k9_yellow_6(A_179,B_180)))
      | ~ v3_pre_topc(C_178,A_179)
      | ~ r2_hidden(B_180,C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2061,plain,(
    ! [C_228,A_229,B_230] :
      ( m1_subset_1(C_228,u1_struct_0(k9_yellow_6(A_229,B_230)))
      | ~ v3_pre_topc(C_228,A_229)
      | ~ r2_hidden(B_230,C_228)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_subset_1(B_230,u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_720,c_28])).

tff(c_48,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2070,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2061,c_48])).

tff(c_2075,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_503,c_2070])).

tff(c_2076,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2075])).

tff(c_2077,plain,(
    ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2076])).

tff(c_2084,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_2077])).

tff(c_2090,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_2084])).

tff(c_2094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_2090])).

tff(c_2095,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2076])).

tff(c_83,plain,(
    ! [B_76,A_77] :
      ( v1_xboole_0(B_76)
      | ~ m1_subset_1(B_76,A_77)
      | ~ v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_83])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_422,plain,(
    ! [C_149,A_150,B_151] :
      ( v3_pre_topc(C_149,A_150)
      | ~ r2_hidden(C_149,u1_struct_0(k9_yellow_6(A_150,B_151)))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_2140,plain,(
    ! [A_233,A_234,B_235] :
      ( v3_pre_topc(A_233,A_234)
      | ~ m1_subset_1(A_233,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ m1_subset_1(B_235,u1_struct_0(A_234))
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234)
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_234,B_235)))
      | ~ m1_subset_1(A_233,u1_struct_0(k9_yellow_6(A_234,B_235))) ) ),
    inference(resolution,[status(thm)],[c_30,c_422])).

tff(c_2154,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_52,c_2140])).

tff(c_2163,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_327,c_2154])).

tff(c_2164,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_60,c_2163])).

tff(c_2157,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_50,c_2140])).

tff(c_2167,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_333,c_2157])).

tff(c_2168,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_60,c_2167])).

tff(c_623,plain,(
    ! [B_167,C_168,A_169] :
      ( v3_pre_topc(k2_xboole_0(B_167,C_168),A_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ v3_pre_topc(C_168,A_169)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ v3_pre_topc(B_167,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_629,plain,(
    ! [B_167] :
      ( v3_pre_topc(k2_xboole_0(B_167,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_167,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_333,c_623])).

tff(c_649,plain,(
    ! [B_167] :
      ( v3_pre_topc(k2_xboole_0(B_167,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_167,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_629])).

tff(c_2415,plain,(
    ! [B_241] :
      ( v3_pre_topc(k2_xboole_0(B_241,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_241,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2168,c_649])).

tff(c_2475,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_327,c_2415])).

tff(c_2511,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2164,c_2475])).

tff(c_2513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2095,c_2511])).

tff(c_2514,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_2709,plain,(
    ! [C_298,A_299,B_300] :
      ( m1_connsp_2(C_298,A_299,B_300)
      | ~ m1_subset_1(C_298,u1_struct_0(k9_yellow_6(A_299,B_300)))
      | ~ m1_subset_1(B_300,u1_struct_0(A_299))
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2723,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2709])).

tff(c_2732,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2723])).

tff(c_2733,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2732])).

tff(c_2741,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2733,c_36])).

tff(c_2744,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2741])).

tff(c_2745,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2744])).

tff(c_2773,plain,(
    ! [C_302,B_303,A_304] :
      ( r2_hidden(C_302,B_303)
      | ~ m1_connsp_2(B_303,A_304,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_304))
      | ~ m1_subset_1(B_303,k1_zfmisc_1(u1_struct_0(A_304)))
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2775,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2733,c_2773])).

tff(c_2780,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2745,c_54,c_2775])).

tff(c_2781,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2780])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2791,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2781,c_2])).

tff(c_2796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_2791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.92  
% 5.01/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.92  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.01/1.92  
% 5.01/1.92  %Foreground sorts:
% 5.01/1.92  
% 5.01/1.92  
% 5.01/1.92  %Background operators:
% 5.01/1.92  
% 5.01/1.92  
% 5.01/1.92  %Foreground operators:
% 5.01/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.01/1.92  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.01/1.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.01/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.01/1.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.01/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.01/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.01/1.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.01/1.92  tff('#skF_5', type, '#skF_5': $i).
% 5.01/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.01/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.01/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.01/1.92  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.01/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.01/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.01/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.01/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.01/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.01/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.01/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/1.92  
% 5.01/1.94  tff(f_182, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.01/1.94  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 5.01/1.94  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.01/1.94  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.01/1.94  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.01/1.94  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.01/1.94  tff(f_68, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.01/1.94  tff(f_62, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.01/1.94  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.01/1.94  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.01/1.94  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.01/1.94  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.01/1.94  tff(f_98, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.01/1.94  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.01/1.94  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_297, plain, (![C_135, A_136, B_137]: (m1_connsp_2(C_135, A_136, B_137) | ~m1_subset_1(C_135, u1_struct_0(k9_yellow_6(A_136, B_137))) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.01/1.94  tff(c_311, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_297])).
% 5.01/1.94  tff(c_320, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_311])).
% 5.01/1.94  tff(c_321, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_320])).
% 5.01/1.94  tff(c_36, plain, (![C_34, A_31, B_32]: (m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_connsp_2(C_34, A_31, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.01/1.94  tff(c_329, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_321, c_36])).
% 5.01/1.94  tff(c_332, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_329])).
% 5.01/1.94  tff(c_333, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_332])).
% 5.01/1.94  tff(c_365, plain, (![C_140, B_141, A_142]: (r2_hidden(C_140, B_141) | ~m1_connsp_2(B_141, A_142, C_140) | ~m1_subset_1(C_140, u1_struct_0(A_142)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.01/1.94  tff(c_367, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_321, c_365])).
% 5.01/1.94  tff(c_372, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_333, c_54, c_367])).
% 5.01/1.94  tff(c_373, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_372])).
% 5.01/1.94  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.94  tff(c_145, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, k2_xboole_0(C_86, B_87)) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.01/1.94  tff(c_10, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | ~r1_tarski(k1_tarski(A_9), B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.01/1.94  tff(c_153, plain, (![A_9, C_86, B_87]: (r2_hidden(A_9, k2_xboole_0(C_86, B_87)) | ~r1_tarski(k1_tarski(A_9), B_87))), inference(resolution, [status(thm)], [c_145, c_10])).
% 5.01/1.94  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_308, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_297])).
% 5.01/1.94  tff(c_316, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_308])).
% 5.01/1.94  tff(c_317, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_316])).
% 5.01/1.94  tff(c_323, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_317, c_36])).
% 5.01/1.94  tff(c_326, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_323])).
% 5.01/1.94  tff(c_327, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_326])).
% 5.01/1.94  tff(c_26, plain, (![A_18, B_19, C_20]: (k4_subset_1(A_18, B_19, C_20)=k2_xboole_0(B_19, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.01/1.94  tff(c_447, plain, (![B_158]: (k4_subset_1(u1_struct_0('#skF_2'), B_158, '#skF_5')=k2_xboole_0(B_158, '#skF_5') | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_333, c_26])).
% 5.01/1.94  tff(c_467, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_327, c_447])).
% 5.01/1.94  tff(c_24, plain, (![A_15, B_16, C_17]: (m1_subset_1(k4_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.01/1.94  tff(c_499, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_467, c_24])).
% 5.01/1.94  tff(c_503, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_333, c_499])).
% 5.01/1.94  tff(c_720, plain, (![C_178, A_179, B_180]: (r2_hidden(C_178, u1_struct_0(k9_yellow_6(A_179, B_180))) | ~v3_pre_topc(C_178, A_179) | ~r2_hidden(B_180, C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.01/1.94  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(A_21, B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.01/1.94  tff(c_2061, plain, (![C_228, A_229, B_230]: (m1_subset_1(C_228, u1_struct_0(k9_yellow_6(A_229, B_230))) | ~v3_pre_topc(C_228, A_229) | ~r2_hidden(B_230, C_228) | ~m1_subset_1(C_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_subset_1(B_230, u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_720, c_28])).
% 5.01/1.94  tff(c_48, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.01/1.94  tff(c_2070, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2061, c_48])).
% 5.01/1.94  tff(c_2075, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_503, c_2070])).
% 5.01/1.94  tff(c_2076, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2075])).
% 5.01/1.94  tff(c_2077, plain, (~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2076])).
% 5.01/1.94  tff(c_2084, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_153, c_2077])).
% 5.01/1.94  tff(c_2090, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_12, c_2084])).
% 5.01/1.94  tff(c_2094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_2090])).
% 5.01/1.94  tff(c_2095, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_2076])).
% 5.01/1.94  tff(c_83, plain, (![B_76, A_77]: (v1_xboole_0(B_76) | ~m1_subset_1(B_76, A_77) | ~v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.01/1.94  tff(c_98, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_83])).
% 5.01/1.94  tff(c_127, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_98])).
% 5.01/1.94  tff(c_30, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | v1_xboole_0(B_24) | ~m1_subset_1(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.01/1.94  tff(c_422, plain, (![C_149, A_150, B_151]: (v3_pre_topc(C_149, A_150) | ~r2_hidden(C_149, u1_struct_0(k9_yellow_6(A_150, B_151))) | ~m1_subset_1(C_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.01/1.94  tff(c_2140, plain, (![A_233, A_234, B_235]: (v3_pre_topc(A_233, A_234) | ~m1_subset_1(A_233, k1_zfmisc_1(u1_struct_0(A_234))) | ~m1_subset_1(B_235, u1_struct_0(A_234)) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_234, B_235))) | ~m1_subset_1(A_233, u1_struct_0(k9_yellow_6(A_234, B_235))))), inference(resolution, [status(thm)], [c_30, c_422])).
% 5.01/1.94  tff(c_2154, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_52, c_2140])).
% 5.01/1.94  tff(c_2163, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_327, c_2154])).
% 5.01/1.94  tff(c_2164, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_127, c_60, c_2163])).
% 5.01/1.94  tff(c_2157, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_50, c_2140])).
% 5.01/1.94  tff(c_2167, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_333, c_2157])).
% 5.01/1.94  tff(c_2168, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_127, c_60, c_2167])).
% 5.01/1.94  tff(c_623, plain, (![B_167, C_168, A_169]: (v3_pre_topc(k2_xboole_0(B_167, C_168), A_169) | ~m1_subset_1(C_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~v3_pre_topc(C_168, A_169) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_169))) | ~v3_pre_topc(B_167, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.01/1.94  tff(c_629, plain, (![B_167]: (v3_pre_topc(k2_xboole_0(B_167, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_167, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_333, c_623])).
% 5.01/1.94  tff(c_649, plain, (![B_167]: (v3_pre_topc(k2_xboole_0(B_167, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_167, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_629])).
% 5.01/1.94  tff(c_2415, plain, (![B_241]: (v3_pre_topc(k2_xboole_0(B_241, '#skF_5'), '#skF_2') | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_241, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2168, c_649])).
% 5.01/1.94  tff(c_2475, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_327, c_2415])).
% 5.01/1.94  tff(c_2511, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2164, c_2475])).
% 5.01/1.94  tff(c_2513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2095, c_2511])).
% 5.01/1.94  tff(c_2514, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_98])).
% 5.01/1.94  tff(c_2709, plain, (![C_298, A_299, B_300]: (m1_connsp_2(C_298, A_299, B_300) | ~m1_subset_1(C_298, u1_struct_0(k9_yellow_6(A_299, B_300))) | ~m1_subset_1(B_300, u1_struct_0(A_299)) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.01/1.94  tff(c_2723, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2709])).
% 5.01/1.94  tff(c_2732, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2723])).
% 5.01/1.94  tff(c_2733, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_2732])).
% 5.01/1.94  tff(c_2741, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2733, c_36])).
% 5.01/1.94  tff(c_2744, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2741])).
% 5.01/1.94  tff(c_2745, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_2744])).
% 5.01/1.94  tff(c_2773, plain, (![C_302, B_303, A_304]: (r2_hidden(C_302, B_303) | ~m1_connsp_2(B_303, A_304, C_302) | ~m1_subset_1(C_302, u1_struct_0(A_304)) | ~m1_subset_1(B_303, k1_zfmisc_1(u1_struct_0(A_304))) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.01/1.94  tff(c_2775, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2733, c_2773])).
% 5.01/1.94  tff(c_2780, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2745, c_54, c_2775])).
% 5.01/1.94  tff(c_2781, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_2780])).
% 5.01/1.94  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.01/1.94  tff(c_2791, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2781, c_2])).
% 5.01/1.94  tff(c_2796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2514, c_2791])).
% 5.01/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/1.94  
% 5.01/1.94  Inference rules
% 5.01/1.94  ----------------------
% 5.01/1.94  #Ref     : 0
% 5.01/1.94  #Sup     : 638
% 5.01/1.94  #Fact    : 0
% 5.01/1.94  #Define  : 0
% 5.01/1.94  #Split   : 8
% 5.01/1.94  #Chain   : 0
% 5.01/1.94  #Close   : 0
% 5.01/1.94  
% 5.01/1.94  Ordering : KBO
% 5.01/1.94  
% 5.01/1.94  Simplification rules
% 5.01/1.94  ----------------------
% 5.01/1.94  #Subsume      : 178
% 5.01/1.94  #Demod        : 346
% 5.01/1.94  #Tautology    : 78
% 5.01/1.94  #SimpNegUnit  : 27
% 5.01/1.94  #BackRed      : 4
% 5.01/1.94  
% 5.01/1.94  #Partial instantiations: 0
% 5.01/1.94  #Strategies tried      : 1
% 5.01/1.94  
% 5.01/1.94  Timing (in seconds)
% 5.01/1.94  ----------------------
% 5.01/1.94  Preprocessing        : 0.35
% 5.01/1.94  Parsing              : 0.19
% 5.01/1.94  CNF conversion       : 0.03
% 5.01/1.94  Main loop            : 0.82
% 5.01/1.94  Inferencing          : 0.28
% 5.01/1.94  Reduction            : 0.28
% 5.01/1.94  Demodulation         : 0.20
% 5.01/1.94  BG Simplification    : 0.03
% 5.01/1.94  Subsumption          : 0.17
% 5.01/1.94  Abstraction          : 0.04
% 5.01/1.94  MUC search           : 0.00
% 5.01/1.94  Cooper               : 0.00
% 5.01/1.94  Total                : 1.20
% 5.01/1.94  Index Insertion      : 0.00
% 5.01/1.94  Index Deletion       : 0.00
% 5.01/1.94  Index Matching       : 0.00
% 5.01/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
