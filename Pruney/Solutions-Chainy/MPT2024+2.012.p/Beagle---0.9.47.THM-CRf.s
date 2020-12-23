%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:15 EST 2020

% Result     : Theorem 25.07s
% Output     : CNFRefutation 25.07s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 607 expanded)
%              Number of leaves         :   40 ( 245 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 (2306 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_177,negated_conjecture,(
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

tff(f_158,axiom,(
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

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_124,axiom,(
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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_143,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_298,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_connsp_2(C_159,A_160,B_161)
      | ~ m1_subset_1(C_159,u1_struct_0(k9_yellow_6(A_160,B_161)))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_305,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_298])).

tff(c_312,plain,
    ( m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_305])).

tff(c_313,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_312])).

tff(c_46,plain,(
    ! [C_31,A_28,B_29] :
      ( m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_connsp_2(C_31,A_28,B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_319,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_46])).

tff(c_322,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_319])).

tff(c_323,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_322])).

tff(c_369,plain,(
    ! [C_162,B_163,A_164] :
      ( r2_hidden(C_162,B_163)
      | ~ m1_connsp_2(B_163,A_164,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_164))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_373,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_313,c_369])).

tff(c_380,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_323,c_64,c_373])).

tff(c_381,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_380])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_308,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_298])).

tff(c_316,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_308])).

tff(c_317,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_316])).

tff(c_325,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_317,c_46])).

tff(c_328,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_325])).

tff(c_329,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_328])).

tff(c_36,plain,(
    ! [A_15,B_16,C_17] :
      ( k4_subset_1(A_15,B_16,C_17) = k2_xboole_0(B_16,C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_587,plain,(
    ! [B_173] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_173,'#skF_6') = k2_xboole_0(B_173,'#skF_6')
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_329,c_36])).

tff(c_603,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_323,c_587])).

tff(c_34,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k4_subset_1(A_12,B_13,C_14),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_647,plain,
    ( m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_34])).

tff(c_651,plain,(
    m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_329,c_647])).

tff(c_74,plain,(
    ! [B_69,A_70] :
      ( v1_xboole_0(B_69)
      | ~ m1_subset_1(B_69,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_85,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_60,c_74])).

tff(c_106,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_1719,plain,(
    ! [B_194,C_195,A_196] :
      ( v3_pre_topc(k2_xboole_0(B_194,C_195),A_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ v3_pre_topc(C_195,A_196)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ v3_pre_topc(B_194,A_196)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1745,plain,(
    ! [B_194] :
      ( v3_pre_topc(k2_xboole_0(B_194,'#skF_5'),'#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_194,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_323,c_1719])).

tff(c_1790,plain,(
    ! [B_194] :
      ( v3_pre_topc(k2_xboole_0(B_194,'#skF_5'),'#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_194,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1745])).

tff(c_43830,plain,(
    ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1790])).

tff(c_28,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1136,plain,(
    ! [C_182,A_183,B_184] :
      ( v3_pre_topc(C_182,A_183)
      | ~ r2_hidden(C_182,u1_struct_0(k9_yellow_6(A_183,B_184)))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64283,plain,(
    ! [B_1527,A_1528,B_1529] :
      ( v3_pre_topc(B_1527,A_1528)
      | ~ m1_subset_1(B_1527,k1_zfmisc_1(u1_struct_0(A_1528)))
      | ~ m1_subset_1(B_1529,u1_struct_0(A_1528))
      | ~ l1_pre_topc(A_1528)
      | ~ v2_pre_topc(A_1528)
      | v2_struct_0(A_1528)
      | ~ m1_subset_1(B_1527,u1_struct_0(k9_yellow_6(A_1528,B_1529)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1528,B_1529))) ) ),
    inference(resolution,[status(thm)],[c_28,c_1136])).

tff(c_64465,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_62,c_64283])).

tff(c_64516,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_323,c_64465])).

tff(c_64518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_70,c_43830,c_64516])).

tff(c_64520,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1790])).

tff(c_1743,plain,(
    ! [B_194] :
      ( v3_pre_topc(k2_xboole_0(B_194,'#skF_6'),'#skF_3')
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_194,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_329,c_1719])).

tff(c_1787,plain,(
    ! [B_194] :
      ( v3_pre_topc(k2_xboole_0(B_194,'#skF_6'),'#skF_3')
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_194,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1743])).

tff(c_3516,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1787])).

tff(c_43587,plain,(
    ! [B_1095,A_1096,B_1097] :
      ( v3_pre_topc(B_1095,A_1096)
      | ~ m1_subset_1(B_1095,k1_zfmisc_1(u1_struct_0(A_1096)))
      | ~ m1_subset_1(B_1097,u1_struct_0(A_1096))
      | ~ l1_pre_topc(A_1096)
      | ~ v2_pre_topc(A_1096)
      | v2_struct_0(A_1096)
      | ~ m1_subset_1(B_1095,u1_struct_0(k9_yellow_6(A_1096,B_1097)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1096,B_1097))) ) ),
    inference(resolution,[status(thm)],[c_28,c_1136])).

tff(c_43772,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_60,c_43587])).

tff(c_43824,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_329,c_43772])).

tff(c_43826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_70,c_3516,c_43824])).

tff(c_65917,plain,(
    ! [B_1567] :
      ( v3_pre_topc(k2_xboole_0(B_1567,'#skF_6'),'#skF_3')
      | ~ m1_subset_1(B_1567,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_1567,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1787])).

tff(c_65961,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_65917])).

tff(c_65987,plain,(
    v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64520,c_65961])).

tff(c_2766,plain,(
    ! [C_224,A_225,B_226] :
      ( r2_hidden(C_224,u1_struct_0(k9_yellow_6(A_225,B_226)))
      | ~ v3_pre_topc(C_224,A_225)
      | ~ r2_hidden(B_226,C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_subset_1(B_226,u1_struct_0(A_225))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83059,plain,(
    ! [C_1922,A_1923,B_1924] :
      ( m1_subset_1(C_1922,u1_struct_0(k9_yellow_6(A_1923,B_1924)))
      | ~ v3_pre_topc(C_1922,A_1923)
      | ~ r2_hidden(B_1924,C_1922)
      | ~ m1_subset_1(C_1922,k1_zfmisc_1(u1_struct_0(A_1923)))
      | ~ m1_subset_1(B_1924,u1_struct_0(A_1923))
      | ~ l1_pre_topc(A_1923)
      | ~ v2_pre_topc(A_1923)
      | v2_struct_0(A_1923) ) ),
    inference(resolution,[status(thm)],[c_2766,c_38])).

tff(c_58,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_83076,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_5','#skF_6'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k2_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_83059,c_58])).

tff(c_83083,plain,
    ( ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_651,c_65987,c_83076])).

tff(c_83084,plain,(
    ~ r2_hidden('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_83083])).

tff(c_83087,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_83084])).

tff(c_83097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_83087])).

tff(c_83099,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_30,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ v1_xboole_0(B_11)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83333,plain,(
    ! [C_2015,A_2016,B_2017] :
      ( m1_connsp_2(C_2015,A_2016,B_2017)
      | ~ m1_subset_1(C_2015,u1_struct_0(k9_yellow_6(A_2016,B_2017)))
      | ~ m1_subset_1(B_2017,u1_struct_0(A_2016))
      | ~ l1_pre_topc(A_2016)
      | ~ v2_pre_topc(A_2016)
      | v2_struct_0(A_2016) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_89433,plain,(
    ! [B_2187,A_2188,B_2189] :
      ( m1_connsp_2(B_2187,A_2188,B_2189)
      | ~ m1_subset_1(B_2189,u1_struct_0(A_2188))
      | ~ l1_pre_topc(A_2188)
      | ~ v2_pre_topc(A_2188)
      | v2_struct_0(A_2188)
      | ~ v1_xboole_0(B_2187)
      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(A_2188,B_2189))) ) ),
    inference(resolution,[status(thm)],[c_30,c_83333])).

tff(c_89435,plain,(
    ! [B_2187] :
      ( m1_connsp_2(B_2187,'#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2187) ) ),
    inference(resolution,[status(thm)],[c_83099,c_89433])).

tff(c_89438,plain,(
    ! [B_2187] :
      ( m1_connsp_2(B_2187,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_89435])).

tff(c_89440,plain,(
    ! [B_2190] :
      ( m1_connsp_2(B_2190,'#skF_3','#skF_4')
      | ~ v1_xboole_0(B_2190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_89438])).

tff(c_89444,plain,(
    ! [B_2190] :
      ( m1_subset_1(B_2190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2190) ) ),
    inference(resolution,[status(thm)],[c_89440,c_46])).

tff(c_89451,plain,(
    ! [B_2190] :
      ( m1_subset_1(B_2190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_89444])).

tff(c_89452,plain,(
    ! [B_2190] :
      ( m1_subset_1(B_2190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_xboole_0(B_2190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_89451])).

tff(c_48,plain,(
    ! [C_38,B_36,A_32] :
      ( r2_hidden(C_38,B_36)
      | ~ m1_connsp_2(B_36,A_32,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_89442,plain,(
    ! [B_2190] :
      ( r2_hidden('#skF_4',B_2190)
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_2190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2190) ) ),
    inference(resolution,[status(thm)],[c_89440,c_48])).

tff(c_89447,plain,(
    ! [B_2190] :
      ( r2_hidden('#skF_4',B_2190)
      | ~ m1_subset_1(B_2190,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ v1_xboole_0(B_2190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_89442])).

tff(c_89570,plain,(
    ! [B_2194] :
      ( r2_hidden('#skF_4',B_2194)
      | ~ m1_subset_1(B_2194,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v1_xboole_0(B_2194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_89447])).

tff(c_89689,plain,(
    ! [B_2195] :
      ( r2_hidden('#skF_4',B_2195)
      | ~ v1_xboole_0(B_2195) ) ),
    inference(resolution,[status(thm)],[c_89452,c_89570])).

tff(c_22,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83644,plain,(
    ! [A_2034,B_2035,C_2036] :
      ( r2_hidden('#skF_1'(A_2034,B_2035,C_2036),B_2035)
      | r2_hidden('#skF_1'(A_2034,B_2035,C_2036),A_2034)
      | r2_hidden('#skF_2'(A_2034,B_2035,C_2036),C_2036)
      | k2_xboole_0(A_2034,B_2035) = C_2036 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_85351,plain,(
    ! [A_2089,B_2090] :
      ( r2_hidden('#skF_1'(A_2089,B_2090,A_2089),B_2090)
      | r2_hidden('#skF_2'(A_2089,B_2090,A_2089),A_2089)
      | k2_xboole_0(A_2089,B_2090) = A_2089 ) ),
    inference(resolution,[status(thm)],[c_83644,c_16])).

tff(c_83963,plain,(
    ! [A_2040,B_2041,C_2042] :
      ( r2_hidden('#skF_1'(A_2040,B_2041,C_2042),B_2041)
      | r2_hidden('#skF_1'(A_2040,B_2041,C_2042),A_2040)
      | ~ r2_hidden('#skF_2'(A_2040,B_2041,C_2042),A_2040)
      | k2_xboole_0(A_2040,B_2041) = C_2042 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84035,plain,(
    ! [A_2040,B_2041] :
      ( r2_hidden('#skF_1'(A_2040,B_2041,A_2040),B_2041)
      | ~ r2_hidden('#skF_2'(A_2040,B_2041,A_2040),A_2040)
      | k2_xboole_0(A_2040,B_2041) = A_2040 ) ),
    inference(resolution,[status(thm)],[c_83963,c_12])).

tff(c_85854,plain,(
    ! [A_2094,B_2095] :
      ( r2_hidden('#skF_1'(A_2094,B_2095,A_2094),B_2095)
      | k2_xboole_0(A_2094,B_2095) = A_2094 ) ),
    inference(resolution,[status(thm)],[c_85351,c_84035])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( ~ r1_tarski(B_24,A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_86153,plain,(
    ! [B_2104,A_2105] :
      ( ~ r1_tarski(B_2104,'#skF_1'(A_2105,B_2104,A_2105))
      | k2_xboole_0(A_2105,B_2104) = A_2105 ) ),
    inference(resolution,[status(thm)],[c_85854,c_42])).

tff(c_86159,plain,(
    ! [A_2106] : k2_xboole_0(A_2106,k1_xboole_0) = A_2106 ),
    inference(resolution,[status(thm)],[c_22,c_86153])).

tff(c_83102,plain,(
    ! [D_1925,B_1926,A_1927] :
      ( ~ r2_hidden(D_1925,B_1926)
      | r2_hidden(D_1925,k2_xboole_0(A_1927,B_1926)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_83110,plain,(
    ! [A_1927,B_1926,D_1925] :
      ( ~ r1_tarski(k2_xboole_0(A_1927,B_1926),D_1925)
      | ~ r2_hidden(D_1925,B_1926) ) ),
    inference(resolution,[status(thm)],[c_83102,c_42])).

tff(c_86207,plain,(
    ! [A_2107,D_2108] :
      ( ~ r1_tarski(A_2107,D_2108)
      | ~ r2_hidden(D_2108,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86159,c_83110])).

tff(c_86210,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_86207])).

tff(c_89719,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_89689,c_86210])).

tff(c_89788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_89719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.07/15.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.07/15.83  
% 25.07/15.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.07/15.84  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 25.07/15.84  
% 25.07/15.84  %Foreground sorts:
% 25.07/15.84  
% 25.07/15.84  
% 25.07/15.84  %Background operators:
% 25.07/15.84  
% 25.07/15.84  
% 25.07/15.84  %Foreground operators:
% 25.07/15.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 25.07/15.84  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 25.07/15.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.07/15.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 25.07/15.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.07/15.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.07/15.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.07/15.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 25.07/15.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.07/15.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.07/15.84  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 25.07/15.84  tff('#skF_5', type, '#skF_5': $i).
% 25.07/15.84  tff('#skF_6', type, '#skF_6': $i).
% 25.07/15.84  tff('#skF_3', type, '#skF_3': $i).
% 25.07/15.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.07/15.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.07/15.84  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 25.07/15.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.07/15.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 25.07/15.84  tff('#skF_4', type, '#skF_4': $i).
% 25.07/15.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.07/15.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 25.07/15.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.07/15.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.07/15.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 25.07/15.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.07/15.84  
% 25.07/15.86  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 25.07/15.86  tff(f_177, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 25.07/15.86  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 25.07/15.86  tff(f_107, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 25.07/15.86  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 25.07/15.86  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 25.07/15.86  tff(f_64, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 25.07/15.86  tff(f_58, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 25.07/15.86  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 25.07/15.86  tff(f_93, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 25.07/15.86  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 25.07/15.86  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 25.07/15.86  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 25.07/15.86  tff(f_79, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 25.07/15.86  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.07/15.86  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_62, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_298, plain, (![C_159, A_160, B_161]: (m1_connsp_2(C_159, A_160, B_161) | ~m1_subset_1(C_159, u1_struct_0(k9_yellow_6(A_160, B_161))) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_158])).
% 25.07/15.86  tff(c_305, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_298])).
% 25.07/15.86  tff(c_312, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_305])).
% 25.07/15.86  tff(c_313, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_312])).
% 25.07/15.86  tff(c_46, plain, (![C_31, A_28, B_29]: (m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_connsp_2(C_31, A_28, B_29) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_107])).
% 25.07/15.86  tff(c_319, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_313, c_46])).
% 25.07/15.86  tff(c_322, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_319])).
% 25.07/15.86  tff(c_323, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_322])).
% 25.07/15.86  tff(c_369, plain, (![C_162, B_163, A_164]: (r2_hidden(C_162, B_163) | ~m1_connsp_2(B_163, A_164, C_162) | ~m1_subset_1(C_162, u1_struct_0(A_164)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.07/15.86  tff(c_373, plain, (r2_hidden('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_313, c_369])).
% 25.07/15.86  tff(c_380, plain, (r2_hidden('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_323, c_64, c_373])).
% 25.07/15.86  tff(c_381, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_380])).
% 25.07/15.86  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_308, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_298])).
% 25.07/15.86  tff(c_316, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_308])).
% 25.07/15.86  tff(c_317, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_316])).
% 25.07/15.86  tff(c_325, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_317, c_46])).
% 25.07/15.86  tff(c_328, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_325])).
% 25.07/15.86  tff(c_329, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_328])).
% 25.07/15.86  tff(c_36, plain, (![A_15, B_16, C_17]: (k4_subset_1(A_15, B_16, C_17)=k2_xboole_0(B_16, C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 25.07/15.86  tff(c_587, plain, (![B_173]: (k4_subset_1(u1_struct_0('#skF_3'), B_173, '#skF_6')=k2_xboole_0(B_173, '#skF_6') | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_329, c_36])).
% 25.07/15.86  tff(c_603, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_5', '#skF_6')=k2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_323, c_587])).
% 25.07/15.86  tff(c_34, plain, (![A_12, B_13, C_14]: (m1_subset_1(k4_subset_1(A_12, B_13, C_14), k1_zfmisc_1(A_12)) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 25.07/15.86  tff(c_647, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_603, c_34])).
% 25.07/15.86  tff(c_651, plain, (m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_329, c_647])).
% 25.07/15.86  tff(c_74, plain, (![B_69, A_70]: (v1_xboole_0(B_69) | ~m1_subset_1(B_69, A_70) | ~v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.07/15.86  tff(c_85, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_60, c_74])).
% 25.07/15.86  tff(c_106, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_85])).
% 25.07/15.86  tff(c_1719, plain, (![B_194, C_195, A_196]: (v3_pre_topc(k2_xboole_0(B_194, C_195), A_196) | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~v3_pre_topc(C_195, A_196) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_196))) | ~v3_pre_topc(B_194, A_196) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_93])).
% 25.07/15.86  tff(c_1745, plain, (![B_194]: (v3_pre_topc(k2_xboole_0(B_194, '#skF_5'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_194, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_323, c_1719])).
% 25.07/15.86  tff(c_1790, plain, (![B_194]: (v3_pre_topc(k2_xboole_0(B_194, '#skF_5'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_194, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1745])).
% 25.07/15.86  tff(c_43830, plain, (~v3_pre_topc('#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_1790])).
% 25.07/15.86  tff(c_28, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.07/15.86  tff(c_1136, plain, (![C_182, A_183, B_184]: (v3_pre_topc(C_182, A_183) | ~r2_hidden(C_182, u1_struct_0(k9_yellow_6(A_183, B_184))) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0(A_183))) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_143])).
% 25.07/15.86  tff(c_64283, plain, (![B_1527, A_1528, B_1529]: (v3_pre_topc(B_1527, A_1528) | ~m1_subset_1(B_1527, k1_zfmisc_1(u1_struct_0(A_1528))) | ~m1_subset_1(B_1529, u1_struct_0(A_1528)) | ~l1_pre_topc(A_1528) | ~v2_pre_topc(A_1528) | v2_struct_0(A_1528) | ~m1_subset_1(B_1527, u1_struct_0(k9_yellow_6(A_1528, B_1529))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1528, B_1529))))), inference(resolution, [status(thm)], [c_28, c_1136])).
% 25.07/15.86  tff(c_64465, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_62, c_64283])).
% 25.07/15.86  tff(c_64516, plain, (v3_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_323, c_64465])).
% 25.07/15.86  tff(c_64518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_70, c_43830, c_64516])).
% 25.07/15.86  tff(c_64520, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_1790])).
% 25.07/15.86  tff(c_1743, plain, (![B_194]: (v3_pre_topc(k2_xboole_0(B_194, '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_194, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_329, c_1719])).
% 25.07/15.86  tff(c_1787, plain, (![B_194]: (v3_pre_topc(k2_xboole_0(B_194, '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_194, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1743])).
% 25.07/15.86  tff(c_3516, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_1787])).
% 25.07/15.86  tff(c_43587, plain, (![B_1095, A_1096, B_1097]: (v3_pre_topc(B_1095, A_1096) | ~m1_subset_1(B_1095, k1_zfmisc_1(u1_struct_0(A_1096))) | ~m1_subset_1(B_1097, u1_struct_0(A_1096)) | ~l1_pre_topc(A_1096) | ~v2_pre_topc(A_1096) | v2_struct_0(A_1096) | ~m1_subset_1(B_1095, u1_struct_0(k9_yellow_6(A_1096, B_1097))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1096, B_1097))))), inference(resolution, [status(thm)], [c_28, c_1136])).
% 25.07/15.86  tff(c_43772, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_60, c_43587])).
% 25.07/15.86  tff(c_43824, plain, (v3_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_329, c_43772])).
% 25.07/15.86  tff(c_43826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_70, c_3516, c_43824])).
% 25.07/15.86  tff(c_65917, plain, (![B_1567]: (v3_pre_topc(k2_xboole_0(B_1567, '#skF_6'), '#skF_3') | ~m1_subset_1(B_1567, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_1567, '#skF_3'))), inference(splitRight, [status(thm)], [c_1787])).
% 25.07/15.86  tff(c_65961, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_323, c_65917])).
% 25.07/15.86  tff(c_65987, plain, (v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64520, c_65961])).
% 25.07/15.86  tff(c_2766, plain, (![C_224, A_225, B_226]: (r2_hidden(C_224, u1_struct_0(k9_yellow_6(A_225, B_226))) | ~v3_pre_topc(C_224, A_225) | ~r2_hidden(B_226, C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(u1_struct_0(A_225))) | ~m1_subset_1(B_226, u1_struct_0(A_225)) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_143])).
% 25.07/15.86  tff(c_38, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 25.07/15.86  tff(c_83059, plain, (![C_1922, A_1923, B_1924]: (m1_subset_1(C_1922, u1_struct_0(k9_yellow_6(A_1923, B_1924))) | ~v3_pre_topc(C_1922, A_1923) | ~r2_hidden(B_1924, C_1922) | ~m1_subset_1(C_1922, k1_zfmisc_1(u1_struct_0(A_1923))) | ~m1_subset_1(B_1924, u1_struct_0(A_1923)) | ~l1_pre_topc(A_1923) | ~v2_pre_topc(A_1923) | v2_struct_0(A_1923))), inference(resolution, [status(thm)], [c_2766, c_38])).
% 25.07/15.86  tff(c_58, plain, (~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 25.07/15.86  tff(c_83076, plain, (~v3_pre_topc(k2_xboole_0('#skF_5', '#skF_6'), '#skF_3') | ~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | ~m1_subset_1(k2_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_83059, c_58])).
% 25.07/15.86  tff(c_83083, plain, (~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_651, c_65987, c_83076])).
% 25.07/15.86  tff(c_83084, plain, (~r2_hidden('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_83083])).
% 25.07/15.86  tff(c_83087, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_83084])).
% 25.07/15.86  tff(c_83097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_381, c_83087])).
% 25.07/15.86  tff(c_83099, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_85])).
% 25.07/15.86  tff(c_30, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~v1_xboole_0(B_11) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 25.07/15.86  tff(c_83333, plain, (![C_2015, A_2016, B_2017]: (m1_connsp_2(C_2015, A_2016, B_2017) | ~m1_subset_1(C_2015, u1_struct_0(k9_yellow_6(A_2016, B_2017))) | ~m1_subset_1(B_2017, u1_struct_0(A_2016)) | ~l1_pre_topc(A_2016) | ~v2_pre_topc(A_2016) | v2_struct_0(A_2016))), inference(cnfTransformation, [status(thm)], [f_158])).
% 25.07/15.86  tff(c_89433, plain, (![B_2187, A_2188, B_2189]: (m1_connsp_2(B_2187, A_2188, B_2189) | ~m1_subset_1(B_2189, u1_struct_0(A_2188)) | ~l1_pre_topc(A_2188) | ~v2_pre_topc(A_2188) | v2_struct_0(A_2188) | ~v1_xboole_0(B_2187) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(A_2188, B_2189))))), inference(resolution, [status(thm)], [c_30, c_83333])).
% 25.07/15.86  tff(c_89435, plain, (![B_2187]: (m1_connsp_2(B_2187, '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2187))), inference(resolution, [status(thm)], [c_83099, c_89433])).
% 25.07/15.86  tff(c_89438, plain, (![B_2187]: (m1_connsp_2(B_2187, '#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2187))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_89435])).
% 25.07/15.86  tff(c_89440, plain, (![B_2190]: (m1_connsp_2(B_2190, '#skF_3', '#skF_4') | ~v1_xboole_0(B_2190))), inference(negUnitSimplification, [status(thm)], [c_70, c_89438])).
% 25.07/15.86  tff(c_89444, plain, (![B_2190]: (m1_subset_1(B_2190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2190))), inference(resolution, [status(thm)], [c_89440, c_46])).
% 25.07/15.86  tff(c_89451, plain, (![B_2190]: (m1_subset_1(B_2190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2190))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_89444])).
% 25.07/15.86  tff(c_89452, plain, (![B_2190]: (m1_subset_1(B_2190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_xboole_0(B_2190))), inference(negUnitSimplification, [status(thm)], [c_70, c_89451])).
% 25.07/15.86  tff(c_48, plain, (![C_38, B_36, A_32]: (r2_hidden(C_38, B_36) | ~m1_connsp_2(B_36, A_32, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_124])).
% 25.07/15.86  tff(c_89442, plain, (![B_2190]: (r2_hidden('#skF_4', B_2190) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1(B_2190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2190))), inference(resolution, [status(thm)], [c_89440, c_48])).
% 25.07/15.86  tff(c_89447, plain, (![B_2190]: (r2_hidden('#skF_4', B_2190) | ~m1_subset_1(B_2190, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~v1_xboole_0(B_2190))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_89442])).
% 25.07/15.86  tff(c_89570, plain, (![B_2194]: (r2_hidden('#skF_4', B_2194) | ~m1_subset_1(B_2194, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_xboole_0(B_2194))), inference(negUnitSimplification, [status(thm)], [c_70, c_89447])).
% 25.07/15.86  tff(c_89689, plain, (![B_2195]: (r2_hidden('#skF_4', B_2195) | ~v1_xboole_0(B_2195))), inference(resolution, [status(thm)], [c_89452, c_89570])).
% 25.07/15.86  tff(c_22, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.07/15.86  tff(c_83644, plain, (![A_2034, B_2035, C_2036]: (r2_hidden('#skF_1'(A_2034, B_2035, C_2036), B_2035) | r2_hidden('#skF_1'(A_2034, B_2035, C_2036), A_2034) | r2_hidden('#skF_2'(A_2034, B_2035, C_2036), C_2036) | k2_xboole_0(A_2034, B_2035)=C_2036)), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_85351, plain, (![A_2089, B_2090]: (r2_hidden('#skF_1'(A_2089, B_2090, A_2089), B_2090) | r2_hidden('#skF_2'(A_2089, B_2090, A_2089), A_2089) | k2_xboole_0(A_2089, B_2090)=A_2089)), inference(resolution, [status(thm)], [c_83644, c_16])).
% 25.07/15.86  tff(c_83963, plain, (![A_2040, B_2041, C_2042]: (r2_hidden('#skF_1'(A_2040, B_2041, C_2042), B_2041) | r2_hidden('#skF_1'(A_2040, B_2041, C_2042), A_2040) | ~r2_hidden('#skF_2'(A_2040, B_2041, C_2042), A_2040) | k2_xboole_0(A_2040, B_2041)=C_2042)), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_84035, plain, (![A_2040, B_2041]: (r2_hidden('#skF_1'(A_2040, B_2041, A_2040), B_2041) | ~r2_hidden('#skF_2'(A_2040, B_2041, A_2040), A_2040) | k2_xboole_0(A_2040, B_2041)=A_2040)), inference(resolution, [status(thm)], [c_83963, c_12])).
% 25.07/15.86  tff(c_85854, plain, (![A_2094, B_2095]: (r2_hidden('#skF_1'(A_2094, B_2095, A_2094), B_2095) | k2_xboole_0(A_2094, B_2095)=A_2094)), inference(resolution, [status(thm)], [c_85351, c_84035])).
% 25.07/15.86  tff(c_42, plain, (![B_24, A_23]: (~r1_tarski(B_24, A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 25.07/15.86  tff(c_86153, plain, (![B_2104, A_2105]: (~r1_tarski(B_2104, '#skF_1'(A_2105, B_2104, A_2105)) | k2_xboole_0(A_2105, B_2104)=A_2105)), inference(resolution, [status(thm)], [c_85854, c_42])).
% 25.07/15.86  tff(c_86159, plain, (![A_2106]: (k2_xboole_0(A_2106, k1_xboole_0)=A_2106)), inference(resolution, [status(thm)], [c_22, c_86153])).
% 25.07/15.86  tff(c_83102, plain, (![D_1925, B_1926, A_1927]: (~r2_hidden(D_1925, B_1926) | r2_hidden(D_1925, k2_xboole_0(A_1927, B_1926)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 25.07/15.86  tff(c_83110, plain, (![A_1927, B_1926, D_1925]: (~r1_tarski(k2_xboole_0(A_1927, B_1926), D_1925) | ~r2_hidden(D_1925, B_1926))), inference(resolution, [status(thm)], [c_83102, c_42])).
% 25.07/15.86  tff(c_86207, plain, (![A_2107, D_2108]: (~r1_tarski(A_2107, D_2108) | ~r2_hidden(D_2108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_86159, c_83110])).
% 25.07/15.86  tff(c_86210, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_86207])).
% 25.07/15.86  tff(c_89719, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_89689, c_86210])).
% 25.07/15.86  tff(c_89788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_89719])).
% 25.07/15.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.07/15.86  
% 25.07/15.86  Inference rules
% 25.07/15.86  ----------------------
% 25.07/15.86  #Ref     : 0
% 25.07/15.86  #Sup     : 18807
% 25.07/15.86  #Fact    : 28
% 25.07/15.86  #Define  : 0
% 25.07/15.86  #Split   : 98
% 25.07/15.86  #Chain   : 0
% 25.07/15.86  #Close   : 0
% 25.07/15.86  
% 25.07/15.86  Ordering : KBO
% 25.07/15.86  
% 25.07/15.86  Simplification rules
% 25.07/15.86  ----------------------
% 25.07/15.86  #Subsume      : 3332
% 25.07/15.86  #Demod        : 6401
% 25.07/15.86  #Tautology    : 2010
% 25.07/15.86  #SimpNegUnit  : 703
% 25.07/15.86  #BackRed      : 787
% 25.07/15.86  
% 25.07/15.86  #Partial instantiations: 0
% 25.07/15.86  #Strategies tried      : 1
% 25.07/15.86  
% 25.07/15.86  Timing (in seconds)
% 25.07/15.86  ----------------------
% 25.07/15.86  Preprocessing        : 0.35
% 25.07/15.86  Parsing              : 0.18
% 25.07/15.86  CNF conversion       : 0.03
% 25.07/15.86  Main loop            : 14.70
% 25.07/15.86  Inferencing          : 2.82
% 25.07/15.86  Reduction            : 5.25
% 25.07/15.86  Demodulation         : 3.99
% 25.07/15.86  BG Simplification    : 0.32
% 25.07/15.86  Subsumption          : 5.25
% 25.07/15.86  Abstraction          : 0.49
% 25.07/15.86  MUC search           : 0.00
% 25.07/15.86  Cooper               : 0.00
% 25.07/15.86  Total                : 15.10
% 25.07/15.86  Index Insertion      : 0.00
% 25.07/15.87  Index Deletion       : 0.00
% 25.07/15.87  Index Matching       : 0.00
% 25.07/15.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
