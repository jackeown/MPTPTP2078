%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 24.70s
% Output     : CNFRefutation 24.88s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 621 expanded)
%              Number of leaves         :   37 ( 248 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 (2358 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_173,negated_conjecture,(
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

tff(f_154,axiom,(
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

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_120,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_139,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_595,plain,(
    ! [C_171,A_172,B_173] :
      ( m1_connsp_2(C_171,A_172,B_173)
      | ~ m1_subset_1(C_171,u1_struct_0(k9_yellow_6(A_172,B_173)))
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_622,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_595])).

tff(c_634,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_622])).

tff(c_635,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_634])).

tff(c_46,plain,(
    ! [C_31,A_28,B_29] :
      ( m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_connsp_2(C_31,A_28,B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_28))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_641,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_635,c_46])).

tff(c_644,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_641])).

tff(c_645,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_644])).

tff(c_687,plain,(
    ! [C_174,B_175,A_176] :
      ( r2_hidden(C_174,B_175)
      | ~ m1_connsp_2(B_175,A_176,C_174)
      | ~ m1_subset_1(C_174,u1_struct_0(A_176))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_691,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_635,c_687])).

tff(c_698,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_645,c_64,c_691])).

tff(c_699,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_698])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( ~ r2_hidden(D_10,A_5)
      | r2_hidden(D_10,k2_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_662,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_645,c_38])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_625,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_595])).

tff(c_638,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_625])).

tff(c_639,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_638])).

tff(c_647,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_639,c_46])).

tff(c_650,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_647])).

tff(c_651,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_650])).

tff(c_673,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_651,c_38])).

tff(c_24,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(k2_xboole_0(A_11,C_13),B_12)
      | ~ r1_tarski(C_13,B_12)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_113,plain,(
    ! [B_78,A_79] :
      ( v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,A_79)
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_113])).

tff(c_139,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_1837,plain,(
    ! [B_240,C_241,A_242] :
      ( v3_pre_topc(k2_xboole_0(B_240,C_241),A_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ v3_pre_topc(C_241,A_242)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ v3_pre_topc(B_240,A_242)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1859,plain,(
    ! [B_240] :
      ( v3_pre_topc(k2_xboole_0(B_240,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_240,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_645,c_1837])).

tff(c_1892,plain,(
    ! [B_240] :
      ( v3_pre_topc(k2_xboole_0(B_240,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_240,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1859])).

tff(c_2131,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1892])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1540,plain,(
    ! [C_227,A_228,B_229] :
      ( v3_pre_topc(C_227,A_228)
      | ~ r2_hidden(C_227,u1_struct_0(k9_yellow_6(A_228,B_229)))
      | ~ m1_subset_1(C_227,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ m1_subset_1(B_229,u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_27120,plain,(
    ! [B_845,A_846,B_847] :
      ( v3_pre_topc(B_845,A_846)
      | ~ m1_subset_1(B_845,k1_zfmisc_1(u1_struct_0(A_846)))
      | ~ m1_subset_1(B_847,u1_struct_0(A_846))
      | ~ l1_pre_topc(A_846)
      | ~ v2_pre_topc(A_846)
      | v2_struct_0(A_846)
      | ~ m1_subset_1(B_845,u1_struct_0(k9_yellow_6(A_846,B_847)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_846,B_847))) ) ),
    inference(resolution,[status(thm)],[c_30,c_1540])).

tff(c_27302,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_62,c_27120])).

tff(c_27353,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_645,c_27302])).

tff(c_27355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_70,c_2131,c_27353])).

tff(c_27357,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1892])).

tff(c_1857,plain,(
    ! [B_240] :
      ( v3_pre_topc(k2_xboole_0(B_240,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_240,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_651,c_1837])).

tff(c_1889,plain,(
    ! [B_240] :
      ( v3_pre_topc(k2_xboole_0(B_240,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_240,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1857])).

tff(c_27428,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1889])).

tff(c_51071,plain,(
    ! [B_1427,A_1428,B_1429] :
      ( v3_pre_topc(B_1427,A_1428)
      | ~ m1_subset_1(B_1427,k1_zfmisc_1(u1_struct_0(A_1428)))
      | ~ m1_subset_1(B_1429,u1_struct_0(A_1428))
      | ~ l1_pre_topc(A_1428)
      | ~ v2_pre_topc(A_1428)
      | v2_struct_0(A_1428)
      | ~ m1_subset_1(B_1427,u1_struct_0(k9_yellow_6(A_1428,B_1429)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1428,B_1429))) ) ),
    inference(resolution,[status(thm)],[c_30,c_1540])).

tff(c_51236,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_51071])).

tff(c_51283,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_651,c_51236])).

tff(c_51285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_70,c_27428,c_51283])).

tff(c_52070,plain,(
    ! [B_1447] :
      ( v3_pre_topc(k2_xboole_0(B_1447,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_1447,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_1447,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1889])).

tff(c_52108,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_645,c_52070])).

tff(c_52150,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27357,c_52108])).

tff(c_51638,plain,(
    ! [C_1440,A_1441,B_1442] :
      ( r2_hidden(C_1440,u1_struct_0(k9_yellow_6(A_1441,B_1442)))
      | ~ v3_pre_topc(C_1440,A_1441)
      | ~ r2_hidden(B_1442,C_1440)
      | ~ m1_subset_1(C_1440,k1_zfmisc_1(u1_struct_0(A_1441)))
      | ~ m1_subset_1(B_1442,u1_struct_0(A_1441))
      | ~ l1_pre_topc(A_1441)
      | ~ v2_pre_topc(A_1441)
      | v2_struct_0(A_1441) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72245,plain,(
    ! [C_1987,A_1988,B_1989] :
      ( m1_subset_1(C_1987,u1_struct_0(k9_yellow_6(A_1988,B_1989)))
      | ~ v3_pre_topc(C_1987,A_1988)
      | ~ r2_hidden(B_1989,C_1987)
      | ~ m1_subset_1(C_1987,k1_zfmisc_1(u1_struct_0(A_1988)))
      | ~ m1_subset_1(B_1989,u1_struct_0(A_1988))
      | ~ l1_pre_topc(A_1988)
      | ~ v2_pre_topc(A_1988)
      | v2_struct_0(A_1988) ) ),
    inference(resolution,[status(thm)],[c_51638,c_36])).

tff(c_58,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_72262,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72245,c_58])).

tff(c_72269,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_52150,c_72262])).

tff(c_72270,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_72269])).

tff(c_72271,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_72270])).

tff(c_72279,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_72271])).

tff(c_72282,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_72279])).

tff(c_72286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_673,c_72282])).

tff(c_72287,plain,(
    ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72270])).

tff(c_72291,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_72287])).

tff(c_72301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_72291])).

tff(c_72302,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_72303,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_72305,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72303,c_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72362,plain,(
    ! [D_2018,B_2019,A_2020] :
      ( r2_hidden(D_2018,B_2019)
      | r2_hidden(D_2018,A_2020)
      | ~ r2_hidden(D_2018,k2_xboole_0(A_2020,B_2019)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72628,plain,(
    ! [A_2074,B_2075] :
      ( r2_hidden('#skF_1'(k2_xboole_0(A_2074,B_2075)),B_2075)
      | r2_hidden('#skF_1'(k2_xboole_0(A_2074,B_2075)),A_2074)
      | v1_xboole_0(k2_xboole_0(A_2074,B_2075)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72362])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72843,plain,(
    ! [A_2084,B_2085] :
      ( ~ v1_xboole_0(A_2084)
      | r2_hidden('#skF_1'(k2_xboole_0(A_2084,B_2085)),B_2085)
      | v1_xboole_0(k2_xboole_0(A_2084,B_2085)) ) ),
    inference(resolution,[status(thm)],[c_72628,c_2])).

tff(c_72960,plain,(
    ! [B_2089,A_2090] :
      ( ~ v1_xboole_0(B_2089)
      | ~ v1_xboole_0(A_2090)
      | v1_xboole_0(k2_xboole_0(A_2090,B_2089)) ) ),
    inference(resolution,[status(thm)],[c_72843,c_2])).

tff(c_93,plain,(
    ! [B_74,A_75] :
      ( m1_subset_1(B_74,A_75)
      | ~ v1_xboole_0(B_74)
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k2_xboole_0('#skF_6','#skF_7'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_93,c_58])).

tff(c_72341,plain,(
    ~ v1_xboole_0(k2_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72303,c_97])).

tff(c_72963,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_72960,c_72341])).

tff(c_72971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72302,c_72305,c_72963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.70/13.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.81/13.46  
% 24.81/13.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.81/13.46  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 24.81/13.46  
% 24.81/13.46  %Foreground sorts:
% 24.81/13.46  
% 24.81/13.46  
% 24.81/13.46  %Background operators:
% 24.81/13.46  
% 24.81/13.46  
% 24.81/13.46  %Foreground operators:
% 24.81/13.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.81/13.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 24.81/13.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 24.81/13.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.81/13.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.81/13.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 24.81/13.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.81/13.46  tff('#skF_7', type, '#skF_7': $i).
% 24.81/13.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.81/13.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.81/13.46  tff('#skF_5', type, '#skF_5': $i).
% 24.81/13.46  tff('#skF_6', type, '#skF_6': $i).
% 24.81/13.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 24.81/13.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.81/13.46  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 24.81/13.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.81/13.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 24.81/13.46  tff('#skF_4', type, '#skF_4': $i).
% 24.81/13.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.81/13.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.81/13.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.81/13.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.81/13.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.81/13.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 24.81/13.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.81/13.46  
% 24.88/13.48  tff(f_173, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_waybel_9)).
% 24.88/13.48  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 24.88/13.48  tff(f_103, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 24.88/13.48  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 24.88/13.48  tff(f_40, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 24.88/13.48  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 24.88/13.48  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 24.88/13.48  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 24.88/13.48  tff(f_89, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_tops_1)).
% 24.88/13.48  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 24.88/13.48  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 24.88/13.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 24.88/13.48  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_62, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_595, plain, (![C_171, A_172, B_173]: (m1_connsp_2(C_171, A_172, B_173) | ~m1_subset_1(C_171, u1_struct_0(k9_yellow_6(A_172, B_173))) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_154])).
% 24.88/13.48  tff(c_622, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_595])).
% 24.88/13.48  tff(c_634, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_622])).
% 24.88/13.48  tff(c_635, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_634])).
% 24.88/13.48  tff(c_46, plain, (![C_31, A_28, B_29]: (m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_connsp_2(C_31, A_28, B_29) | ~m1_subset_1(B_29, u1_struct_0(A_28)) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_103])).
% 24.88/13.48  tff(c_641, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_635, c_46])).
% 24.88/13.48  tff(c_644, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_641])).
% 24.88/13.48  tff(c_645, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_644])).
% 24.88/13.48  tff(c_687, plain, (![C_174, B_175, A_176]: (r2_hidden(C_174, B_175) | ~m1_connsp_2(B_175, A_176, C_174) | ~m1_subset_1(C_174, u1_struct_0(A_176)) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_120])).
% 24.88/13.48  tff(c_691, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_635, c_687])).
% 24.88/13.48  tff(c_698, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_645, c_64, c_691])).
% 24.88/13.48  tff(c_699, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_698])).
% 24.88/13.48  tff(c_10, plain, (![D_10, A_5, B_6]: (~r2_hidden(D_10, A_5) | r2_hidden(D_10, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 24.88/13.48  tff(c_38, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.88/13.48  tff(c_662, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_645, c_38])).
% 24.88/13.48  tff(c_60, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_625, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_595])).
% 24.88/13.48  tff(c_638, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_625])).
% 24.88/13.48  tff(c_639, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_638])).
% 24.88/13.48  tff(c_647, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_639, c_46])).
% 24.88/13.48  tff(c_650, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_647])).
% 24.88/13.48  tff(c_651, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_650])).
% 24.88/13.48  tff(c_673, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_651, c_38])).
% 24.88/13.48  tff(c_24, plain, (![A_11, C_13, B_12]: (r1_tarski(k2_xboole_0(A_11, C_13), B_12) | ~r1_tarski(C_13, B_12) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 24.88/13.48  tff(c_40, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 24.88/13.48  tff(c_113, plain, (![B_78, A_79]: (v1_xboole_0(B_78) | ~m1_subset_1(B_78, A_79) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 24.88/13.48  tff(c_135, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_113])).
% 24.88/13.48  tff(c_139, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_135])).
% 24.88/13.48  tff(c_1837, plain, (![B_240, C_241, A_242]: (v3_pre_topc(k2_xboole_0(B_240, C_241), A_242) | ~m1_subset_1(C_241, k1_zfmisc_1(u1_struct_0(A_242))) | ~v3_pre_topc(C_241, A_242) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_242))) | ~v3_pre_topc(B_240, A_242) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_89])).
% 24.88/13.48  tff(c_1859, plain, (![B_240]: (v3_pre_topc(k2_xboole_0(B_240, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_240, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_645, c_1837])).
% 24.88/13.48  tff(c_1892, plain, (![B_240]: (v3_pre_topc(k2_xboole_0(B_240, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_240, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1859])).
% 24.88/13.48  tff(c_2131, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1892])).
% 24.88/13.48  tff(c_30, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 24.88/13.48  tff(c_1540, plain, (![C_227, A_228, B_229]: (v3_pre_topc(C_227, A_228) | ~r2_hidden(C_227, u1_struct_0(k9_yellow_6(A_228, B_229))) | ~m1_subset_1(C_227, k1_zfmisc_1(u1_struct_0(A_228))) | ~m1_subset_1(B_229, u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_139])).
% 24.88/13.48  tff(c_27120, plain, (![B_845, A_846, B_847]: (v3_pre_topc(B_845, A_846) | ~m1_subset_1(B_845, k1_zfmisc_1(u1_struct_0(A_846))) | ~m1_subset_1(B_847, u1_struct_0(A_846)) | ~l1_pre_topc(A_846) | ~v2_pre_topc(A_846) | v2_struct_0(A_846) | ~m1_subset_1(B_845, u1_struct_0(k9_yellow_6(A_846, B_847))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_846, B_847))))), inference(resolution, [status(thm)], [c_30, c_1540])).
% 24.88/13.48  tff(c_27302, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_62, c_27120])).
% 24.88/13.48  tff(c_27353, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_645, c_27302])).
% 24.88/13.48  tff(c_27355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_70, c_2131, c_27353])).
% 24.88/13.48  tff(c_27357, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_1892])).
% 24.88/13.48  tff(c_1857, plain, (![B_240]: (v3_pre_topc(k2_xboole_0(B_240, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_240, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_651, c_1837])).
% 24.88/13.48  tff(c_1889, plain, (![B_240]: (v3_pre_topc(k2_xboole_0(B_240, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_240, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1857])).
% 24.88/13.48  tff(c_27428, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_1889])).
% 24.88/13.48  tff(c_51071, plain, (![B_1427, A_1428, B_1429]: (v3_pre_topc(B_1427, A_1428) | ~m1_subset_1(B_1427, k1_zfmisc_1(u1_struct_0(A_1428))) | ~m1_subset_1(B_1429, u1_struct_0(A_1428)) | ~l1_pre_topc(A_1428) | ~v2_pre_topc(A_1428) | v2_struct_0(A_1428) | ~m1_subset_1(B_1427, u1_struct_0(k9_yellow_6(A_1428, B_1429))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1428, B_1429))))), inference(resolution, [status(thm)], [c_30, c_1540])).
% 24.88/13.48  tff(c_51236, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_51071])).
% 24.88/13.48  tff(c_51283, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_651, c_51236])).
% 24.88/13.48  tff(c_51285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_70, c_27428, c_51283])).
% 24.88/13.48  tff(c_52070, plain, (![B_1447]: (v3_pre_topc(k2_xboole_0(B_1447, '#skF_7'), '#skF_4') | ~m1_subset_1(B_1447, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_1447, '#skF_4'))), inference(splitRight, [status(thm)], [c_1889])).
% 24.88/13.48  tff(c_52108, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_645, c_52070])).
% 24.88/13.48  tff(c_52150, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27357, c_52108])).
% 24.88/13.48  tff(c_51638, plain, (![C_1440, A_1441, B_1442]: (r2_hidden(C_1440, u1_struct_0(k9_yellow_6(A_1441, B_1442))) | ~v3_pre_topc(C_1440, A_1441) | ~r2_hidden(B_1442, C_1440) | ~m1_subset_1(C_1440, k1_zfmisc_1(u1_struct_0(A_1441))) | ~m1_subset_1(B_1442, u1_struct_0(A_1441)) | ~l1_pre_topc(A_1441) | ~v2_pre_topc(A_1441) | v2_struct_0(A_1441))), inference(cnfTransformation, [status(thm)], [f_139])).
% 24.88/13.48  tff(c_36, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 24.88/13.48  tff(c_72245, plain, (![C_1987, A_1988, B_1989]: (m1_subset_1(C_1987, u1_struct_0(k9_yellow_6(A_1988, B_1989))) | ~v3_pre_topc(C_1987, A_1988) | ~r2_hidden(B_1989, C_1987) | ~m1_subset_1(C_1987, k1_zfmisc_1(u1_struct_0(A_1988))) | ~m1_subset_1(B_1989, u1_struct_0(A_1988)) | ~l1_pre_topc(A_1988) | ~v2_pre_topc(A_1988) | v2_struct_0(A_1988))), inference(resolution, [status(thm)], [c_51638, c_36])).
% 24.88/13.48  tff(c_58, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 24.88/13.48  tff(c_72262, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72245, c_58])).
% 24.88/13.48  tff(c_72269, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_52150, c_72262])).
% 24.88/13.48  tff(c_72270, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_72269])).
% 24.88/13.48  tff(c_72271, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_72270])).
% 24.88/13.48  tff(c_72279, plain, (~r1_tarski(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_72271])).
% 24.88/13.48  tff(c_72282, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_4')) | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_72279])).
% 24.88/13.48  tff(c_72286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_662, c_673, c_72282])).
% 24.88/13.48  tff(c_72287, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_72270])).
% 24.88/13.48  tff(c_72291, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_10, c_72287])).
% 24.88/13.48  tff(c_72301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_699, c_72291])).
% 24.88/13.48  tff(c_72302, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_135])).
% 24.88/13.48  tff(c_72303, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_135])).
% 24.88/13.48  tff(c_136, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_113])).
% 24.88/13.48  tff(c_72305, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72303, c_136])).
% 24.88/13.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.88/13.48  tff(c_72362, plain, (![D_2018, B_2019, A_2020]: (r2_hidden(D_2018, B_2019) | r2_hidden(D_2018, A_2020) | ~r2_hidden(D_2018, k2_xboole_0(A_2020, B_2019)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 24.88/13.48  tff(c_72628, plain, (![A_2074, B_2075]: (r2_hidden('#skF_1'(k2_xboole_0(A_2074, B_2075)), B_2075) | r2_hidden('#skF_1'(k2_xboole_0(A_2074, B_2075)), A_2074) | v1_xboole_0(k2_xboole_0(A_2074, B_2075)))), inference(resolution, [status(thm)], [c_4, c_72362])).
% 24.88/13.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.88/13.48  tff(c_72843, plain, (![A_2084, B_2085]: (~v1_xboole_0(A_2084) | r2_hidden('#skF_1'(k2_xboole_0(A_2084, B_2085)), B_2085) | v1_xboole_0(k2_xboole_0(A_2084, B_2085)))), inference(resolution, [status(thm)], [c_72628, c_2])).
% 24.88/13.48  tff(c_72960, plain, (![B_2089, A_2090]: (~v1_xboole_0(B_2089) | ~v1_xboole_0(A_2090) | v1_xboole_0(k2_xboole_0(A_2090, B_2089)))), inference(resolution, [status(thm)], [c_72843, c_2])).
% 24.88/13.48  tff(c_93, plain, (![B_74, A_75]: (m1_subset_1(B_74, A_75) | ~v1_xboole_0(B_74) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_61])).
% 24.88/13.48  tff(c_97, plain, (~v1_xboole_0(k2_xboole_0('#skF_6', '#skF_7')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_93, c_58])).
% 24.88/13.48  tff(c_72341, plain, (~v1_xboole_0(k2_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72303, c_97])).
% 24.88/13.48  tff(c_72963, plain, (~v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_72960, c_72341])).
% 24.88/13.48  tff(c_72971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72302, c_72305, c_72963])).
% 24.88/13.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.88/13.48  
% 24.88/13.48  Inference rules
% 24.88/13.48  ----------------------
% 24.88/13.48  #Ref     : 0
% 24.88/13.48  #Sup     : 18150
% 24.88/13.48  #Fact    : 28
% 24.88/13.48  #Define  : 0
% 24.88/13.48  #Split   : 63
% 24.88/13.48  #Chain   : 0
% 24.88/13.48  #Close   : 0
% 24.88/13.48  
% 24.88/13.48  Ordering : KBO
% 24.88/13.48  
% 24.88/13.48  Simplification rules
% 24.88/13.48  ----------------------
% 24.88/13.48  #Subsume      : 7202
% 24.88/13.48  #Demod        : 3347
% 24.88/13.48  #Tautology    : 2518
% 24.88/13.48  #SimpNegUnit  : 719
% 24.88/13.48  #BackRed      : 76
% 24.88/13.48  
% 24.88/13.48  #Partial instantiations: 0
% 24.88/13.48  #Strategies tried      : 1
% 24.88/13.48  
% 24.88/13.48  Timing (in seconds)
% 24.88/13.48  ----------------------
% 24.88/13.48  Preprocessing        : 0.32
% 24.88/13.48  Parsing              : 0.17
% 24.88/13.48  CNF conversion       : 0.03
% 24.88/13.48  Main loop            : 12.36
% 24.88/13.48  Inferencing          : 2.19
% 24.88/13.48  Reduction            : 2.61
% 24.88/13.48  Demodulation         : 1.80
% 24.88/13.48  BG Simplification    : 0.23
% 24.88/13.48  Subsumption          : 6.58
% 24.88/13.48  Abstraction          : 0.38
% 24.88/13.48  MUC search           : 0.00
% 24.88/13.48  Cooper               : 0.00
% 24.88/13.48  Total                : 12.72
% 24.88/13.48  Index Insertion      : 0.00
% 24.88/13.48  Index Deletion       : 0.00
% 24.88/13.48  Index Matching       : 0.00
% 24.88/13.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
