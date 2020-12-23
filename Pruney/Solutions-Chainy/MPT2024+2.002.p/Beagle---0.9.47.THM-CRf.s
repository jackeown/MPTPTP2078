%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 532 expanded)
%              Number of leaves         :   42 ( 215 expanded)
%              Depth                    :   18
%              Number of atoms          :  341 (1875 expanded)
%              Number of equality atoms :   15 (  29 expanded)
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

tff(f_192,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_139,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_723,plain,(
    ! [C_163,A_164,B_165] :
      ( m1_connsp_2(C_163,A_164,B_165)
      | ~ m1_subset_1(C_163,u1_struct_0(k9_yellow_6(A_164,B_165)))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_738,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_723])).

tff(c_747,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_738])).

tff(c_748,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_747])).

tff(c_44,plain,(
    ! [C_40,A_37,B_38] :
      ( m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_connsp_2(C_40,A_37,B_38)
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_754,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_748,c_44])).

tff(c_757,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_754])).

tff(c_758,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_757])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_741,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_723])).

tff(c_751,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_741])).

tff(c_752,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_751])).

tff(c_760,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_752,c_44])).

tff(c_763,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_760])).

tff(c_764,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_763])).

tff(c_36,plain,(
    ! [A_26,B_27,C_28] :
      ( k4_subset_1(A_26,B_27,C_28) = k2_xboole_0(B_27,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1006,plain,(
    ! [B_186] :
      ( k4_subset_1(u1_struct_0('#skF_2'),B_186,'#skF_5') = k2_xboole_0(B_186,'#skF_5')
      | ~ m1_subset_1(B_186,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_764,c_36])).

tff(c_1035,plain,(
    k4_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_758,c_1006])).

tff(c_34,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_subset_1(k4_subset_1(A_23,B_24,C_25),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(A_23))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1054,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_34])).

tff(c_1058,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_764,c_1054])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(A_89,B_90) = B_90
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_160,plain,(
    ! [B_6] : k2_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_148])).

tff(c_339,plain,(
    ! [A_111,B_112] :
      ( r2_hidden(A_111,B_112)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_111),B_112),B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_350,plain,(
    ! [A_111] :
      ( r2_hidden(A_111,k1_tarski(A_111))
      | ~ r1_tarski(k1_tarski(A_111),k1_tarski(A_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_339])).

tff(c_357,plain,(
    ! [A_113] : r2_hidden(A_113,k1_tarski(A_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_350])).

tff(c_38,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_364,plain,(
    ! [A_113] : m1_subset_1(A_113,k1_tarski(A_113)) ),
    inference(resolution,[status(thm)],[c_357,c_38])).

tff(c_786,plain,(
    ! [C_166,B_167,A_168] :
      ( r2_hidden(C_166,B_167)
      | ~ m1_connsp_2(B_167,A_168,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0(A_168))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_790,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_748,c_786])).

tff(c_797,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_758,c_62,c_790])).

tff(c_798,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_797])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_365,plain,(
    ! [A_113] : ~ v1_xboole_0(k1_tarski(A_113)) ),
    inference(resolution,[status(thm)],[c_357,c_2])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r2_hidden(B_22,A_21)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_252,plain,(
    ! [A_105,B_106] :
      ( k2_xboole_0(k1_tarski(A_105),B_106) = B_106
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_268,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k1_tarski(A_105),B_106)
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_16])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_516,plain,(
    ! [A_137,C_138,B_139] :
      ( r1_tarski(k1_tarski(A_137),C_138)
      | ~ r1_tarski(B_139,C_138)
      | ~ r2_hidden(A_137,B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_12])).

tff(c_588,plain,(
    ! [A_149,B_150,A_151] :
      ( r1_tarski(k1_tarski(A_149),B_150)
      | ~ r2_hidden(A_149,k1_tarski(A_151))
      | ~ r2_hidden(A_151,B_150) ) ),
    inference(resolution,[status(thm)],[c_268,c_516])).

tff(c_593,plain,(
    ! [B_22,B_150,A_151] :
      ( r1_tarski(k1_tarski(B_22),B_150)
      | ~ r2_hidden(A_151,B_150)
      | ~ m1_subset_1(B_22,k1_tarski(A_151))
      | v1_xboole_0(k1_tarski(A_151)) ) ),
    inference(resolution,[status(thm)],[c_28,c_588])).

tff(c_962,plain,(
    ! [B_181,B_182,A_183] :
      ( r1_tarski(k1_tarski(B_181),B_182)
      | ~ r2_hidden(A_183,B_182)
      | ~ m1_subset_1(B_181,k1_tarski(A_183)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_593])).

tff(c_984,plain,(
    ! [B_184] :
      ( r1_tarski(k1_tarski(B_184),'#skF_4')
      | ~ m1_subset_1(B_184,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_798,c_962])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1093,plain,(
    ! [B_189] :
      ( k2_xboole_0(k1_tarski(B_189),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_189,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_984,c_14])).

tff(c_1111,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_364,c_1093])).

tff(c_205,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(A_97,C_98)
      | ~ r1_tarski(k2_xboole_0(A_97,B_99),C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_97,B_99,B_13] : r1_tarski(A_97,k2_xboole_0(k2_xboole_0(A_97,B_99),B_13)) ),
    inference(resolution,[status(thm)],[c_16,c_205])).

tff(c_1221,plain,(
    ! [B_193] : r1_tarski(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_217])).

tff(c_2771,plain,(
    ! [B_269] : k2_xboole_0(k1_tarski('#skF_3'),k2_xboole_0('#skF_4',B_269)) = k2_xboole_0('#skF_4',B_269) ),
    inference(resolution,[status(thm)],[c_1221,c_14])).

tff(c_159,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(resolution,[status(thm)],[c_16,c_148])).

tff(c_343,plain,(
    ! [A_111,B_13] :
      ( r2_hidden(A_111,k2_xboole_0(k1_tarski(A_111),B_13))
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_111),B_13),k2_xboole_0(k1_tarski(A_111),B_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_339])).

tff(c_352,plain,(
    ! [A_111,B_13] : r2_hidden(A_111,k2_xboole_0(k1_tarski(A_111),B_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_343])).

tff(c_2800,plain,(
    ! [B_269] : r2_hidden('#skF_3',k2_xboole_0('#skF_4',B_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2771,c_352])).

tff(c_1421,plain,(
    ! [C_196,A_197,B_198] :
      ( r2_hidden(C_196,u1_struct_0(k9_yellow_6(A_197,B_198)))
      | ~ v3_pre_topc(C_196,A_197)
      | ~ r2_hidden(B_198,C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3351,plain,(
    ! [C_290,A_291,B_292] :
      ( m1_subset_1(C_290,u1_struct_0(k9_yellow_6(A_291,B_292)))
      | ~ v3_pre_topc(C_290,A_291)
      | ~ r2_hidden(B_292,C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ m1_subset_1(B_292,u1_struct_0(A_291))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_1421,c_38])).

tff(c_56,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_3357,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3351,c_56])).

tff(c_3364,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1058,c_2800,c_3357])).

tff(c_3365,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3364])).

tff(c_93,plain,(
    ! [B_83,A_84] :
      ( v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,A_84)
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_60,c_93])).

tff(c_195,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_946,plain,(
    ! [C_178,A_179,B_180] :
      ( v3_pre_topc(C_178,A_179)
      | ~ r2_hidden(C_178,u1_struct_0(k9_yellow_6(A_179,B_180)))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3549,plain,(
    ! [B_299,A_300,B_301] :
      ( v3_pre_topc(B_299,A_300)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_subset_1(B_301,u1_struct_0(A_300))
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300)
      | v2_struct_0(A_300)
      | ~ m1_subset_1(B_299,u1_struct_0(k9_yellow_6(A_300,B_301)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_300,B_301))) ) ),
    inference(resolution,[status(thm)],[c_28,c_946])).

tff(c_3567,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_60,c_3549])).

tff(c_3577,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_758,c_3567])).

tff(c_3578,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_68,c_3577])).

tff(c_3570,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_3549])).

tff(c_3581,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | v2_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_764,c_3570])).

tff(c_3582,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_68,c_3581])).

tff(c_1116,plain,(
    ! [B_190,C_191,A_192] :
      ( v3_pre_topc(k2_xboole_0(B_190,C_191),A_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v3_pre_topc(C_191,A_192)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ v3_pre_topc(B_190,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1122,plain,(
    ! [B_190] :
      ( v3_pre_topc(k2_xboole_0(B_190,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_190,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_764,c_1116])).

tff(c_1145,plain,(
    ! [B_190] :
      ( v3_pre_topc(k2_xboole_0(B_190,'#skF_5'),'#skF_2')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_190,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1122])).

tff(c_3868,plain,(
    ! [B_310] :
      ( v3_pre_topc(k2_xboole_0(B_310,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(B_310,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_pre_topc(B_310,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3582,c_1145])).

tff(c_3892,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_758,c_3868])).

tff(c_3920,plain,(
    v3_pre_topc(k2_xboole_0('#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3578,c_3892])).

tff(c_3922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3365,c_3920])).

tff(c_3924,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_58,c_93])).

tff(c_3926,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3924,c_108])).

tff(c_4456,plain,(
    ! [C_379,A_380,B_381] :
      ( m1_connsp_2(C_379,A_380,B_381)
      | ~ m1_subset_1(C_379,u1_struct_0(k9_yellow_6(A_380,B_381)))
      | ~ m1_subset_1(B_381,u1_struct_0(A_380))
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_4474,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_4456])).

tff(c_4484,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_4474])).

tff(c_4485,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4484])).

tff(c_4493,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4485,c_44])).

tff(c_4496,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_4493])).

tff(c_4497,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4496])).

tff(c_4577,plain,(
    ! [C_391,B_392,A_393] :
      ( r2_hidden(C_391,B_392)
      | ~ m1_connsp_2(B_392,A_393,C_391)
      | ~ m1_subset_1(C_391,u1_struct_0(A_393))
      | ~ m1_subset_1(B_392,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4579,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4485,c_4577])).

tff(c_4584,plain,
    ( r2_hidden('#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4497,c_62,c_4579])).

tff(c_4585,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4584])).

tff(c_4597,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4585,c_2])).

tff(c_4603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3926,c_4597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.07  
% 5.65/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.07  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.65/2.07  
% 5.65/2.07  %Foreground sorts:
% 5.65/2.07  
% 5.65/2.07  
% 5.65/2.07  %Background operators:
% 5.65/2.07  
% 5.65/2.07  
% 5.65/2.07  %Foreground operators:
% 5.65/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.65/2.07  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.65/2.07  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.65/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.65/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.65/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.65/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.65/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.65/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.65/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.65/2.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.65/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.65/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.65/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.65/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.65/2.07  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 5.65/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.65/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.65/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.65/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.65/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.65/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.65/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.65/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.65/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.65/2.07  
% 5.65/2.09  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 5.65/2.09  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 5.65/2.09  tff(f_122, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.65/2.09  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.65/2.09  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.65/2.09  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.65/2.09  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.65/2.09  tff(f_53, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 5.65/2.09  tff(f_88, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.65/2.09  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 5.65/2.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.65/2.09  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.65/2.09  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 5.65/2.09  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.65/2.09  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.65/2.09  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 5.65/2.09  tff(f_108, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 5.65/2.09  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_62, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_60, plain, (m1_subset_1('#skF_4', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_723, plain, (![C_163, A_164, B_165]: (m1_connsp_2(C_163, A_164, B_165) | ~m1_subset_1(C_163, u1_struct_0(k9_yellow_6(A_164, B_165))) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.65/2.09  tff(c_738, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_723])).
% 5.65/2.09  tff(c_747, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_738])).
% 5.65/2.09  tff(c_748, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_747])).
% 5.65/2.09  tff(c_44, plain, (![C_40, A_37, B_38]: (m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_connsp_2(C_40, A_37, B_38) | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.65/2.09  tff(c_754, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_748, c_44])).
% 5.65/2.09  tff(c_757, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_754])).
% 5.65/2.09  tff(c_758, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_757])).
% 5.65/2.09  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.09  tff(c_741, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_723])).
% 5.65/2.09  tff(c_751, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_741])).
% 5.65/2.09  tff(c_752, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_751])).
% 5.65/2.09  tff(c_760, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_752, c_44])).
% 5.65/2.09  tff(c_763, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_760])).
% 5.65/2.09  tff(c_764, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_763])).
% 5.65/2.09  tff(c_36, plain, (![A_26, B_27, C_28]: (k4_subset_1(A_26, B_27, C_28)=k2_xboole_0(B_27, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.65/2.09  tff(c_1006, plain, (![B_186]: (k4_subset_1(u1_struct_0('#skF_2'), B_186, '#skF_5')=k2_xboole_0(B_186, '#skF_5') | ~m1_subset_1(B_186, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_764, c_36])).
% 5.65/2.09  tff(c_1035, plain, (k4_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_758, c_1006])).
% 5.65/2.09  tff(c_34, plain, (![A_23, B_24, C_25]: (m1_subset_1(k4_subset_1(A_23, B_24, C_25), k1_zfmisc_1(A_23)) | ~m1_subset_1(C_25, k1_zfmisc_1(A_23)) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.65/2.09  tff(c_1054, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_34])).
% 5.65/2.09  tff(c_1058, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_758, c_764, c_1054])).
% 5.65/2.09  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.65/2.09  tff(c_148, plain, (![A_89, B_90]: (k2_xboole_0(A_89, B_90)=B_90 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.65/2.09  tff(c_160, plain, (![B_6]: (k2_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_148])).
% 5.65/2.09  tff(c_339, plain, (![A_111, B_112]: (r2_hidden(A_111, B_112) | ~r1_tarski(k2_xboole_0(k1_tarski(A_111), B_112), B_112))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.65/2.09  tff(c_350, plain, (![A_111]: (r2_hidden(A_111, k1_tarski(A_111)) | ~r1_tarski(k1_tarski(A_111), k1_tarski(A_111)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_339])).
% 5.65/2.09  tff(c_357, plain, (![A_113]: (r2_hidden(A_113, k1_tarski(A_113)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_350])).
% 5.65/2.09  tff(c_38, plain, (![A_29, B_30]: (m1_subset_1(A_29, B_30) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.65/2.09  tff(c_364, plain, (![A_113]: (m1_subset_1(A_113, k1_tarski(A_113)))), inference(resolution, [status(thm)], [c_357, c_38])).
% 5.65/2.09  tff(c_786, plain, (![C_166, B_167, A_168]: (r2_hidden(C_166, B_167) | ~m1_connsp_2(B_167, A_168, C_166) | ~m1_subset_1(C_166, u1_struct_0(A_168)) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_168))) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.65/2.09  tff(c_790, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_748, c_786])).
% 5.65/2.09  tff(c_797, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_758, c_62, c_790])).
% 5.65/2.09  tff(c_798, plain, (r2_hidden('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_797])).
% 5.65/2.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.65/2.09  tff(c_365, plain, (![A_113]: (~v1_xboole_0(k1_tarski(A_113)))), inference(resolution, [status(thm)], [c_357, c_2])).
% 5.65/2.09  tff(c_28, plain, (![B_22, A_21]: (r2_hidden(B_22, A_21) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.65/2.09  tff(c_252, plain, (![A_105, B_106]: (k2_xboole_0(k1_tarski(A_105), B_106)=B_106 | ~r2_hidden(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.65/2.09  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.65/2.09  tff(c_268, plain, (![A_105, B_106]: (r1_tarski(k1_tarski(A_105), B_106) | ~r2_hidden(A_105, B_106))), inference(superposition, [status(thm), theory('equality')], [c_252, c_16])).
% 5.65/2.09  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.09  tff(c_516, plain, (![A_137, C_138, B_139]: (r1_tarski(k1_tarski(A_137), C_138) | ~r1_tarski(B_139, C_138) | ~r2_hidden(A_137, B_139))), inference(superposition, [status(thm), theory('equality')], [c_252, c_12])).
% 5.65/2.09  tff(c_588, plain, (![A_149, B_150, A_151]: (r1_tarski(k1_tarski(A_149), B_150) | ~r2_hidden(A_149, k1_tarski(A_151)) | ~r2_hidden(A_151, B_150))), inference(resolution, [status(thm)], [c_268, c_516])).
% 5.65/2.09  tff(c_593, plain, (![B_22, B_150, A_151]: (r1_tarski(k1_tarski(B_22), B_150) | ~r2_hidden(A_151, B_150) | ~m1_subset_1(B_22, k1_tarski(A_151)) | v1_xboole_0(k1_tarski(A_151)))), inference(resolution, [status(thm)], [c_28, c_588])).
% 5.65/2.09  tff(c_962, plain, (![B_181, B_182, A_183]: (r1_tarski(k1_tarski(B_181), B_182) | ~r2_hidden(A_183, B_182) | ~m1_subset_1(B_181, k1_tarski(A_183)))), inference(negUnitSimplification, [status(thm)], [c_365, c_593])).
% 5.65/2.09  tff(c_984, plain, (![B_184]: (r1_tarski(k1_tarski(B_184), '#skF_4') | ~m1_subset_1(B_184, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_798, c_962])).
% 5.65/2.09  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.65/2.09  tff(c_1093, plain, (![B_189]: (k2_xboole_0(k1_tarski(B_189), '#skF_4')='#skF_4' | ~m1_subset_1(B_189, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_984, c_14])).
% 5.65/2.09  tff(c_1111, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_364, c_1093])).
% 5.65/2.09  tff(c_205, plain, (![A_97, C_98, B_99]: (r1_tarski(A_97, C_98) | ~r1_tarski(k2_xboole_0(A_97, B_99), C_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.10  tff(c_217, plain, (![A_97, B_99, B_13]: (r1_tarski(A_97, k2_xboole_0(k2_xboole_0(A_97, B_99), B_13)))), inference(resolution, [status(thm)], [c_16, c_205])).
% 5.65/2.10  tff(c_1221, plain, (![B_193]: (r1_tarski(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', B_193)))), inference(superposition, [status(thm), theory('equality')], [c_1111, c_217])).
% 5.65/2.10  tff(c_2771, plain, (![B_269]: (k2_xboole_0(k1_tarski('#skF_3'), k2_xboole_0('#skF_4', B_269))=k2_xboole_0('#skF_4', B_269))), inference(resolution, [status(thm)], [c_1221, c_14])).
% 5.65/2.10  tff(c_159, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_16, c_148])).
% 5.65/2.10  tff(c_343, plain, (![A_111, B_13]: (r2_hidden(A_111, k2_xboole_0(k1_tarski(A_111), B_13)) | ~r1_tarski(k2_xboole_0(k1_tarski(A_111), B_13), k2_xboole_0(k1_tarski(A_111), B_13)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_339])).
% 5.65/2.10  tff(c_352, plain, (![A_111, B_13]: (r2_hidden(A_111, k2_xboole_0(k1_tarski(A_111), B_13)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_343])).
% 5.65/2.10  tff(c_2800, plain, (![B_269]: (r2_hidden('#skF_3', k2_xboole_0('#skF_4', B_269)))), inference(superposition, [status(thm), theory('equality')], [c_2771, c_352])).
% 5.65/2.10  tff(c_1421, plain, (![C_196, A_197, B_198]: (r2_hidden(C_196, u1_struct_0(k9_yellow_6(A_197, B_198))) | ~v3_pre_topc(C_196, A_197) | ~r2_hidden(B_198, C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.65/2.10  tff(c_3351, plain, (![C_290, A_291, B_292]: (m1_subset_1(C_290, u1_struct_0(k9_yellow_6(A_291, B_292))) | ~v3_pre_topc(C_290, A_291) | ~r2_hidden(B_292, C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~m1_subset_1(B_292, u1_struct_0(A_291)) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_1421, c_38])).
% 5.65/2.10  tff(c_56, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.65/2.10  tff(c_3357, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden('#skF_3', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3351, c_56])).
% 5.65/2.10  tff(c_3364, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1058, c_2800, c_3357])).
% 5.65/2.10  tff(c_3365, plain, (~v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_3364])).
% 5.65/2.10  tff(c_93, plain, (![B_83, A_84]: (v1_xboole_0(B_83) | ~m1_subset_1(B_83, A_84) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.65/2.10  tff(c_107, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_60, c_93])).
% 5.65/2.10  tff(c_195, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_107])).
% 5.65/2.10  tff(c_946, plain, (![C_178, A_179, B_180]: (v3_pre_topc(C_178, A_179) | ~r2_hidden(C_178, u1_struct_0(k9_yellow_6(A_179, B_180))) | ~m1_subset_1(C_178, k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.65/2.10  tff(c_3549, plain, (![B_299, A_300, B_301]: (v3_pre_topc(B_299, A_300) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_300))) | ~m1_subset_1(B_301, u1_struct_0(A_300)) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300) | v2_struct_0(A_300) | ~m1_subset_1(B_299, u1_struct_0(k9_yellow_6(A_300, B_301))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_300, B_301))))), inference(resolution, [status(thm)], [c_28, c_946])).
% 5.65/2.10  tff(c_3567, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_60, c_3549])).
% 5.65/2.10  tff(c_3577, plain, (v3_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_758, c_3567])).
% 5.65/2.10  tff(c_3578, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_195, c_68, c_3577])).
% 5.65/2.10  tff(c_3570, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_58, c_3549])).
% 5.65/2.10  tff(c_3581, plain, (v3_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_764, c_3570])).
% 5.65/2.10  tff(c_3582, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_195, c_68, c_3581])).
% 5.65/2.10  tff(c_1116, plain, (![B_190, C_191, A_192]: (v3_pre_topc(k2_xboole_0(B_190, C_191), A_192) | ~m1_subset_1(C_191, k1_zfmisc_1(u1_struct_0(A_192))) | ~v3_pre_topc(C_191, A_192) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_192))) | ~v3_pre_topc(B_190, A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.65/2.10  tff(c_1122, plain, (![B_190]: (v3_pre_topc(k2_xboole_0(B_190, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_190, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_764, c_1116])).
% 5.65/2.10  tff(c_1145, plain, (![B_190]: (v3_pre_topc(k2_xboole_0(B_190, '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_190, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1122])).
% 5.65/2.10  tff(c_3868, plain, (![B_310]: (v3_pre_topc(k2_xboole_0(B_310, '#skF_5'), '#skF_2') | ~m1_subset_1(B_310, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_pre_topc(B_310, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3582, c_1145])).
% 5.65/2.10  tff(c_3892, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_758, c_3868])).
% 5.65/2.10  tff(c_3920, plain, (v3_pre_topc(k2_xboole_0('#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3578, c_3892])).
% 5.65/2.10  tff(c_3922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3365, c_3920])).
% 5.65/2.10  tff(c_3924, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_107])).
% 5.65/2.10  tff(c_108, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_58, c_93])).
% 5.65/2.10  tff(c_3926, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3924, c_108])).
% 5.65/2.10  tff(c_4456, plain, (![C_379, A_380, B_381]: (m1_connsp_2(C_379, A_380, B_381) | ~m1_subset_1(C_379, u1_struct_0(k9_yellow_6(A_380, B_381))) | ~m1_subset_1(B_381, u1_struct_0(A_380)) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.65/2.10  tff(c_4474, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_4456])).
% 5.65/2.10  tff(c_4484, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_4474])).
% 5.65/2.10  tff(c_4485, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_4484])).
% 5.65/2.10  tff(c_4493, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4485, c_44])).
% 5.65/2.10  tff(c_4496, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_4493])).
% 5.65/2.10  tff(c_4497, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_68, c_4496])).
% 5.65/2.10  tff(c_4577, plain, (![C_391, B_392, A_393]: (r2_hidden(C_391, B_392) | ~m1_connsp_2(B_392, A_393, C_391) | ~m1_subset_1(C_391, u1_struct_0(A_393)) | ~m1_subset_1(B_392, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_139])).
% 5.65/2.10  tff(c_4579, plain, (r2_hidden('#skF_3', '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4485, c_4577])).
% 5.65/2.10  tff(c_4584, plain, (r2_hidden('#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4497, c_62, c_4579])).
% 5.65/2.10  tff(c_4585, plain, (r2_hidden('#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_4584])).
% 5.65/2.10  tff(c_4597, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4585, c_2])).
% 5.65/2.10  tff(c_4603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3926, c_4597])).
% 5.65/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.10  
% 5.65/2.10  Inference rules
% 5.65/2.10  ----------------------
% 5.65/2.10  #Ref     : 0
% 5.65/2.10  #Sup     : 1051
% 5.65/2.10  #Fact    : 0
% 5.65/2.10  #Define  : 0
% 5.65/2.10  #Split   : 5
% 5.65/2.10  #Chain   : 0
% 5.65/2.10  #Close   : 0
% 5.65/2.10  
% 5.65/2.10  Ordering : KBO
% 5.65/2.10  
% 5.65/2.10  Simplification rules
% 5.65/2.10  ----------------------
% 5.65/2.10  #Subsume      : 204
% 5.65/2.10  #Demod        : 487
% 5.65/2.10  #Tautology    : 346
% 5.65/2.10  #SimpNegUnit  : 44
% 5.65/2.10  #BackRed      : 2
% 5.65/2.10  
% 5.65/2.10  #Partial instantiations: 0
% 5.65/2.10  #Strategies tried      : 1
% 5.65/2.10  
% 5.65/2.10  Timing (in seconds)
% 5.65/2.10  ----------------------
% 5.65/2.10  Preprocessing        : 0.34
% 5.65/2.10  Parsing              : 0.18
% 5.65/2.10  CNF conversion       : 0.03
% 5.65/2.10  Main loop            : 0.98
% 5.65/2.10  Inferencing          : 0.33
% 5.65/2.10  Reduction            : 0.34
% 5.65/2.10  Demodulation         : 0.24
% 5.65/2.10  BG Simplification    : 0.04
% 5.65/2.10  Subsumption          : 0.21
% 5.65/2.10  Abstraction          : 0.04
% 5.65/2.10  MUC search           : 0.00
% 5.65/2.10  Cooper               : 0.00
% 5.65/2.10  Total                : 1.37
% 5.65/2.10  Index Insertion      : 0.00
% 5.65/2.10  Index Deletion       : 0.00
% 5.65/2.10  Index Matching       : 0.00
% 5.65/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
