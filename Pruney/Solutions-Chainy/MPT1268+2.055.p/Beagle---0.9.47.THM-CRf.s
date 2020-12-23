%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:54 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 4.77s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 288 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   20
%              Number of atoms          :  226 ( 818 expanded)
%              Number of equality atoms :   31 ( 108 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B,C] :
          ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,k1_tops_1(A,C))
          <=> ? [D] :
                ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                & v3_pre_topc(D,A)
                & r1_tarski(D,C)
                & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_116,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k1_tops_1(A_57,B_58),B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_125,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_204,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k1_tops_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_209,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_204])).

tff(c_213,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_209])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_129,plain,(
    k2_xboole_0(k1_tops_1('#skF_3','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_125,c_6])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [C_5] :
      ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),C_5)
      | ~ r1_tarski('#skF_4',C_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [C_40] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_40
      | ~ v3_pre_topc(C_40,'#skF_3')
      | ~ r1_tarski(C_40,'#skF_4')
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_216,plain,(
    ! [C_69] :
      ( k1_xboole_0 = C_69
      | ~ v3_pre_topc(C_69,'#skF_3')
      | ~ r1_tarski(C_69,'#skF_4')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58])).

tff(c_226,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ v3_pre_topc(A_70,'#skF_3')
      | ~ r1_tarski(A_70,'#skF_4')
      | ~ r1_tarski(A_70,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_216])).

tff(c_234,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_133,c_226])).

tff(c_245,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_125,c_213,c_234])).

tff(c_272,plain,(
    ! [B_71,A_72] :
      ( v2_tops_1(B_71,A_72)
      | k1_tops_1(A_72,B_71) != k1_xboole_0
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_279,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_272])).

tff(c_283,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_245,c_279])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_286,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_287,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_289,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_42])).

tff(c_44,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_297,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_44])).

tff(c_46,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_333,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_46])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_373,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(k1_tops_1(A_87,B_88),B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_532,plain,(
    ! [A_101,A_102] :
      ( r1_tarski(k1_tops_1(A_101,A_102),A_102)
      | ~ l1_pre_topc(A_101)
      | ~ r1_tarski(A_102,u1_struct_0(A_101)) ) ),
    inference(resolution,[status(thm)],[c_12,c_373])).

tff(c_682,plain,(
    ! [A_114,A_115] :
      ( k2_xboole_0(k1_tops_1(A_114,A_115),A_115) = A_115
      | ~ l1_pre_topc(A_114)
      | ~ r1_tarski(A_115,u1_struct_0(A_114)) ) ),
    inference(resolution,[status(thm)],[c_532,c_6])).

tff(c_718,plain,(
    ! [A_116] :
      ( k2_xboole_0(k1_tops_1(A_116,k1_xboole_0),k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_682])).

tff(c_724,plain,(
    ! [A_116,C_5] :
      ( r1_tarski(k1_tops_1(A_116,k1_xboole_0),C_5)
      | ~ r1_tarski(k1_xboole_0,C_5)
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_4])).

tff(c_732,plain,(
    ! [A_117,C_118] :
      ( r1_tarski(k1_tops_1(A_117,k1_xboole_0),C_118)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_724])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_291,plain,(
    ! [B_74,A_75] :
      ( ~ r1_tarski(B_74,A_75)
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_295,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_291])).

tff(c_749,plain,(
    ! [A_119] :
      ( k1_tops_1(A_119,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_732,c_295])).

tff(c_753,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_749])).

tff(c_22,plain,(
    ! [B_25,A_18,C_26] :
      ( r2_hidden(B_25,'#skF_2'(A_18,B_25,C_26))
      | ~ r2_hidden(B_25,k1_tops_1(A_18,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_762,plain,(
    ! [B_25] :
      ( r2_hidden(B_25,'#skF_2'('#skF_3',B_25,k1_xboole_0))
      | ~ r2_hidden(B_25,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_22])).

tff(c_773,plain,(
    ! [B_25] :
      ( r2_hidden(B_25,'#skF_2'('#skF_3',B_25,k1_xboole_0))
      | ~ r2_hidden(B_25,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_762])).

tff(c_820,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_773])).

tff(c_823,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_820])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_823])).

tff(c_829,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_777,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski('#skF_2'(A_120,B_121,C_122),C_122)
      | ~ r2_hidden(B_121,k1_tops_1(A_120,C_122))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_779,plain,(
    ! [B_121] :
      ( r1_tarski('#skF_2'('#skF_3',B_121,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_121,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_777])).

tff(c_786,plain,(
    ! [B_121] :
      ( r1_tarski('#skF_2'('#skF_3',B_121,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_121,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_779])).

tff(c_998,plain,(
    ! [B_145] :
      ( r1_tarski('#skF_2'('#skF_3',B_145,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(B_145,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_786])).

tff(c_1011,plain,(
    ! [B_146] :
      ( k2_xboole_0('#skF_2'('#skF_3',B_146,k1_xboole_0),k1_xboole_0) = k1_xboole_0
      | ~ r2_hidden(B_146,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_998,c_6])).

tff(c_1017,plain,(
    ! [B_146,C_5] :
      ( r1_tarski('#skF_2'('#skF_3',B_146,k1_xboole_0),C_5)
      | ~ r1_tarski(k1_xboole_0,C_5)
      | ~ r2_hidden(B_146,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_4])).

tff(c_1025,plain,(
    ! [B_147,C_148] :
      ( r1_tarski('#skF_2'('#skF_3',B_147,k1_xboole_0),C_148)
      | ~ r2_hidden(B_147,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1017])).

tff(c_857,plain,(
    ! [B_126] :
      ( r2_hidden(B_126,'#skF_2'('#skF_3',B_126,k1_xboole_0))
      | ~ r2_hidden(B_126,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_861,plain,(
    ! [B_126] :
      ( ~ r1_tarski('#skF_2'('#skF_3',B_126,k1_xboole_0),B_126)
      | ~ r2_hidden(B_126,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_857,c_14])).

tff(c_1042,plain,(
    ! [C_148] : ~ r2_hidden(C_148,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1025,c_861])).

tff(c_571,plain,(
    ! [A_105,B_106] :
      ( k1_tops_1(A_105,B_106) = k1_xboole_0
      | ~ v2_tops_1(B_106,A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_581,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_571])).

tff(c_589,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_287,c_581])).

tff(c_1054,plain,(
    ! [B_150,A_151,C_152,D_153] :
      ( r2_hidden(B_150,k1_tops_1(A_151,C_152))
      | ~ r2_hidden(B_150,D_153)
      | ~ r1_tarski(D_153,C_152)
      | ~ v3_pre_topc(D_153,A_151)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2348,plain,(
    ! [A_229,A_230,C_231] :
      ( r2_hidden('#skF_1'(A_229),k1_tops_1(A_230,C_231))
      | ~ r1_tarski(A_229,C_231)
      | ~ v3_pre_topc(A_229,A_230)
      | ~ m1_subset_1(A_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | k1_xboole_0 = A_229 ) ),
    inference(resolution,[status(thm)],[c_2,c_1054])).

tff(c_2363,plain,(
    ! [A_229] :
      ( r2_hidden('#skF_1'(A_229),k1_xboole_0)
      | ~ r1_tarski(A_229,'#skF_4')
      | ~ v3_pre_topc(A_229,'#skF_3')
      | ~ m1_subset_1(A_229,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | k1_xboole_0 = A_229 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_2348])).

tff(c_2372,plain,(
    ! [A_229] :
      ( r2_hidden('#skF_1'(A_229),k1_xboole_0)
      | ~ r1_tarski(A_229,'#skF_4')
      | ~ v3_pre_topc(A_229,'#skF_3')
      | ~ m1_subset_1(A_229,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_229 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_2363])).

tff(c_2374,plain,(
    ! [A_232] :
      ( ~ r1_tarski(A_232,'#skF_4')
      | ~ v3_pre_topc(A_232,'#skF_3')
      | ~ m1_subset_1(A_232,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k1_xboole_0 = A_232 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_2372])).

tff(c_2384,plain,
    ( ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_333,c_2374])).

tff(c_2401,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_297,c_2384])).

tff(c_2403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_2401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.85  
% 4.77/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.85  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.77/1.85  
% 4.77/1.85  %Foreground sorts:
% 4.77/1.85  
% 4.77/1.85  
% 4.77/1.85  %Background operators:
% 4.77/1.85  
% 4.77/1.85  
% 4.77/1.85  %Foreground operators:
% 4.77/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.77/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.77/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.77/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.77/1.85  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.77/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.77/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.77/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.77/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.77/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.77/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.85  
% 4.77/1.88  tff(f_113, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 4.77/1.88  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.77/1.88  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.77/1.88  tff(f_60, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.77/1.88  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.77/1.88  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.77/1.88  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.77/1.88  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.77/1.88  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.77/1.88  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.77/1.88  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 4.77/1.88  tff(c_40, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_60, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 4.77/1.88  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_74, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.77/1.88  tff(c_78, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_74])).
% 4.77/1.88  tff(c_116, plain, (![A_57, B_58]: (r1_tarski(k1_tops_1(A_57, B_58), B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.88  tff(c_121, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_116])).
% 4.77/1.88  tff(c_125, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 4.77/1.88  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_204, plain, (![A_67, B_68]: (v3_pre_topc(k1_tops_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.77/1.88  tff(c_209, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_204])).
% 4.77/1.88  tff(c_213, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_209])).
% 4.77/1.88  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.77/1.88  tff(c_129, plain, (k2_xboole_0(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_125, c_6])).
% 4.77/1.88  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.77/1.88  tff(c_133, plain, (![C_5]: (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), C_5) | ~r1_tarski('#skF_4', C_5))), inference(superposition, [status(thm), theory('equality')], [c_129, c_4])).
% 4.77/1.88  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.77/1.88  tff(c_58, plain, (![C_40]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_40 | ~v3_pre_topc(C_40, '#skF_3') | ~r1_tarski(C_40, '#skF_4') | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_216, plain, (![C_69]: (k1_xboole_0=C_69 | ~v3_pre_topc(C_69, '#skF_3') | ~r1_tarski(C_69, '#skF_4') | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_58])).
% 4.77/1.88  tff(c_226, plain, (![A_70]: (k1_xboole_0=A_70 | ~v3_pre_topc(A_70, '#skF_3') | ~r1_tarski(A_70, '#skF_4') | ~r1_tarski(A_70, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_216])).
% 4.77/1.88  tff(c_234, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_133, c_226])).
% 4.77/1.88  tff(c_245, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_125, c_213, c_234])).
% 4.77/1.88  tff(c_272, plain, (![B_71, A_72]: (v2_tops_1(B_71, A_72) | k1_tops_1(A_72, B_71)!=k1_xboole_0 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.77/1.88  tff(c_279, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_272])).
% 4.77/1.88  tff(c_283, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_245, c_279])).
% 4.77/1.88  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 4.77/1.88  tff(c_286, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 4.77/1.88  tff(c_287, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.77/1.88  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_289, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_42])).
% 4.77/1.88  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_297, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_44])).
% 4.77/1.88  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.77/1.88  tff(c_333, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_46])).
% 4.77/1.88  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.77/1.88  tff(c_373, plain, (![A_87, B_88]: (r1_tarski(k1_tops_1(A_87, B_88), B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.77/1.88  tff(c_532, plain, (![A_101, A_102]: (r1_tarski(k1_tops_1(A_101, A_102), A_102) | ~l1_pre_topc(A_101) | ~r1_tarski(A_102, u1_struct_0(A_101)))), inference(resolution, [status(thm)], [c_12, c_373])).
% 4.77/1.88  tff(c_682, plain, (![A_114, A_115]: (k2_xboole_0(k1_tops_1(A_114, A_115), A_115)=A_115 | ~l1_pre_topc(A_114) | ~r1_tarski(A_115, u1_struct_0(A_114)))), inference(resolution, [status(thm)], [c_532, c_6])).
% 4.77/1.88  tff(c_718, plain, (![A_116]: (k2_xboole_0(k1_tops_1(A_116, k1_xboole_0), k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_8, c_682])).
% 4.77/1.88  tff(c_724, plain, (![A_116, C_5]: (r1_tarski(k1_tops_1(A_116, k1_xboole_0), C_5) | ~r1_tarski(k1_xboole_0, C_5) | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_718, c_4])).
% 4.77/1.88  tff(c_732, plain, (![A_117, C_118]: (r1_tarski(k1_tops_1(A_117, k1_xboole_0), C_118) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_724])).
% 4.77/1.88  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.77/1.88  tff(c_291, plain, (![B_74, A_75]: (~r1_tarski(B_74, A_75) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/1.88  tff(c_295, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_291])).
% 4.77/1.88  tff(c_749, plain, (![A_119]: (k1_tops_1(A_119, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_732, c_295])).
% 4.77/1.88  tff(c_753, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_749])).
% 4.77/1.88  tff(c_22, plain, (![B_25, A_18, C_26]: (r2_hidden(B_25, '#skF_2'(A_18, B_25, C_26)) | ~r2_hidden(B_25, k1_tops_1(A_18, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.88  tff(c_762, plain, (![B_25]: (r2_hidden(B_25, '#skF_2'('#skF_3', B_25, k1_xboole_0)) | ~r2_hidden(B_25, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_22])).
% 4.77/1.88  tff(c_773, plain, (![B_25]: (r2_hidden(B_25, '#skF_2'('#skF_3', B_25, k1_xboole_0)) | ~r2_hidden(B_25, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_762])).
% 4.77/1.88  tff(c_820, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_773])).
% 4.77/1.88  tff(c_823, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_820])).
% 4.77/1.88  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_823])).
% 4.77/1.88  tff(c_829, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_773])).
% 4.77/1.88  tff(c_777, plain, (![A_120, B_121, C_122]: (r1_tarski('#skF_2'(A_120, B_121, C_122), C_122) | ~r2_hidden(B_121, k1_tops_1(A_120, C_122)) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.88  tff(c_779, plain, (![B_121]: (r1_tarski('#skF_2'('#skF_3', B_121, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_121, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_753, c_777])).
% 4.77/1.88  tff(c_786, plain, (![B_121]: (r1_tarski('#skF_2'('#skF_3', B_121, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_121, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_779])).
% 4.77/1.88  tff(c_998, plain, (![B_145]: (r1_tarski('#skF_2'('#skF_3', B_145, k1_xboole_0), k1_xboole_0) | ~r2_hidden(B_145, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_829, c_786])).
% 4.77/1.88  tff(c_1011, plain, (![B_146]: (k2_xboole_0('#skF_2'('#skF_3', B_146, k1_xboole_0), k1_xboole_0)=k1_xboole_0 | ~r2_hidden(B_146, k1_xboole_0))), inference(resolution, [status(thm)], [c_998, c_6])).
% 4.77/1.88  tff(c_1017, plain, (![B_146, C_5]: (r1_tarski('#skF_2'('#skF_3', B_146, k1_xboole_0), C_5) | ~r1_tarski(k1_xboole_0, C_5) | ~r2_hidden(B_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1011, c_4])).
% 4.77/1.88  tff(c_1025, plain, (![B_147, C_148]: (r1_tarski('#skF_2'('#skF_3', B_147, k1_xboole_0), C_148) | ~r2_hidden(B_147, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1017])).
% 4.77/1.88  tff(c_857, plain, (![B_126]: (r2_hidden(B_126, '#skF_2'('#skF_3', B_126, k1_xboole_0)) | ~r2_hidden(B_126, k1_xboole_0))), inference(splitRight, [status(thm)], [c_773])).
% 4.77/1.88  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.77/1.88  tff(c_861, plain, (![B_126]: (~r1_tarski('#skF_2'('#skF_3', B_126, k1_xboole_0), B_126) | ~r2_hidden(B_126, k1_xboole_0))), inference(resolution, [status(thm)], [c_857, c_14])).
% 4.77/1.88  tff(c_1042, plain, (![C_148]: (~r2_hidden(C_148, k1_xboole_0))), inference(resolution, [status(thm)], [c_1025, c_861])).
% 4.77/1.88  tff(c_571, plain, (![A_105, B_106]: (k1_tops_1(A_105, B_106)=k1_xboole_0 | ~v2_tops_1(B_106, A_105) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.77/1.88  tff(c_581, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_571])).
% 4.77/1.88  tff(c_589, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_287, c_581])).
% 4.77/1.88  tff(c_1054, plain, (![B_150, A_151, C_152, D_153]: (r2_hidden(B_150, k1_tops_1(A_151, C_152)) | ~r2_hidden(B_150, D_153) | ~r1_tarski(D_153, C_152) | ~v3_pre_topc(D_153, A_151) | ~m1_subset_1(D_153, k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_subset_1(C_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.77/1.88  tff(c_2348, plain, (![A_229, A_230, C_231]: (r2_hidden('#skF_1'(A_229), k1_tops_1(A_230, C_231)) | ~r1_tarski(A_229, C_231) | ~v3_pre_topc(A_229, A_230) | ~m1_subset_1(A_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | k1_xboole_0=A_229)), inference(resolution, [status(thm)], [c_2, c_1054])).
% 4.77/1.88  tff(c_2363, plain, (![A_229]: (r2_hidden('#skF_1'(A_229), k1_xboole_0) | ~r1_tarski(A_229, '#skF_4') | ~v3_pre_topc(A_229, '#skF_3') | ~m1_subset_1(A_229, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | k1_xboole_0=A_229)), inference(superposition, [status(thm), theory('equality')], [c_589, c_2348])).
% 4.77/1.88  tff(c_2372, plain, (![A_229]: (r2_hidden('#skF_1'(A_229), k1_xboole_0) | ~r1_tarski(A_229, '#skF_4') | ~v3_pre_topc(A_229, '#skF_3') | ~m1_subset_1(A_229, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_229)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_2363])).
% 4.77/1.88  tff(c_2374, plain, (![A_232]: (~r1_tarski(A_232, '#skF_4') | ~v3_pre_topc(A_232, '#skF_3') | ~m1_subset_1(A_232, k1_zfmisc_1(u1_struct_0('#skF_3'))) | k1_xboole_0=A_232)), inference(negUnitSimplification, [status(thm)], [c_1042, c_2372])).
% 4.77/1.88  tff(c_2384, plain, (~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_3') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_333, c_2374])).
% 4.77/1.88  tff(c_2401, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_297, c_2384])).
% 4.77/1.88  tff(c_2403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_2401])).
% 4.77/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.88  
% 4.77/1.88  Inference rules
% 4.77/1.88  ----------------------
% 4.77/1.88  #Ref     : 0
% 4.77/1.88  #Sup     : 524
% 4.77/1.88  #Fact    : 0
% 4.77/1.88  #Define  : 0
% 4.77/1.88  #Split   : 20
% 4.77/1.88  #Chain   : 0
% 4.77/1.88  #Close   : 0
% 4.77/1.88  
% 4.77/1.88  Ordering : KBO
% 4.77/1.88  
% 4.77/1.88  Simplification rules
% 4.77/1.88  ----------------------
% 4.77/1.88  #Subsume      : 131
% 4.77/1.88  #Demod        : 295
% 4.77/1.88  #Tautology    : 186
% 4.77/1.88  #SimpNegUnit  : 25
% 4.77/1.88  #BackRed      : 13
% 4.77/1.88  
% 4.77/1.88  #Partial instantiations: 0
% 4.77/1.88  #Strategies tried      : 1
% 4.77/1.88  
% 4.77/1.88  Timing (in seconds)
% 4.77/1.88  ----------------------
% 4.77/1.88  Preprocessing        : 0.31
% 4.77/1.88  Parsing              : 0.17
% 4.77/1.88  CNF conversion       : 0.02
% 4.77/1.88  Main loop            : 0.80
% 4.77/1.88  Inferencing          : 0.26
% 4.77/1.88  Reduction            : 0.26
% 4.77/1.88  Demodulation         : 0.18
% 4.77/1.88  BG Simplification    : 0.03
% 4.77/1.88  Subsumption          : 0.19
% 4.77/1.88  Abstraction          : 0.03
% 4.77/1.88  MUC search           : 0.00
% 4.77/1.88  Cooper               : 0.00
% 4.77/1.88  Total                : 1.16
% 4.77/1.88  Index Insertion      : 0.00
% 4.77/1.88  Index Deletion       : 0.00
% 4.77/1.88  Index Matching       : 0.00
% 4.77/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
