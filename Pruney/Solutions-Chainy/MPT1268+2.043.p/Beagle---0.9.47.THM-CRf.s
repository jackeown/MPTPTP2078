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
% DateTime   : Thu Dec  3 10:21:52 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 169 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 520 expanded)
%              Number of equality atoms :   26 (  69 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_133,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_65,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_105,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_60,plain,(
    ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_136,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k1_tops_1(A_79,B_80),B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_145,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_228,plain,(
    ! [A_90,B_91] :
      ( v3_pre_topc(k1_tops_1(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_233,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_237,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_233])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_74,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_74])).

tff(c_111,plain,(
    ! [A_73,C_74,B_75] :
      ( r1_tarski(A_73,C_74)
      | ~ r1_tarski(B_75,C_74)
      | ~ r1_tarski(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_111])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_208,plain,(
    ! [A_88,A_89] :
      ( r1_tarski(A_88,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_88,A_89)
      | ~ r1_tarski(A_89,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_10])).

tff(c_210,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_208])).

tff(c_221,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_210])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [C_53] :
      ( v2_tops_1('#skF_4','#skF_3')
      | k1_xboole_0 = C_53
      | ~ v3_pre_topc(C_53,'#skF_3')
      | ~ r1_tarski(C_53,'#skF_4')
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_171,plain,(
    ! [C_84] :
      ( k1_xboole_0 = C_84
      | ~ v3_pre_topc(C_84,'#skF_3')
      | ~ r1_tarski(C_84,'#skF_4')
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58])).

tff(c_448,plain,(
    ! [A_111] :
      ( k1_xboole_0 = A_111
      | ~ v3_pre_topc(A_111,'#skF_3')
      | ~ r1_tarski(A_111,'#skF_4')
      | ~ r1_tarski(A_111,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_459,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_448])).

tff(c_478,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_237,c_459])).

tff(c_512,plain,(
    ! [B_113,A_114] :
      ( v2_tops_1(B_113,A_114)
      | k1_tops_1(A_114,B_113) != k1_xboole_0
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_519,plain,
    ( v2_tops_1('#skF_4','#skF_3')
    | k1_tops_1('#skF_3','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_512])).

tff(c_523,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_478,c_519])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_523])).

tff(c_526,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_527,plain,(
    v2_tops_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_532,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_44])).

tff(c_953,plain,(
    ! [A_164,B_165] :
      ( k1_tops_1(A_164,B_165) = k1_xboole_0
      | ~ v2_tops_1(B_165,A_164)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_963,plain,
    ( k1_tops_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ v2_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_953])).

tff(c_970,plain,(
    k1_tops_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_527,c_963])).

tff(c_46,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_556,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_46])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ v2_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_529,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_42])).

tff(c_28,plain,(
    ! [B_36,D_42,C_40,A_28] :
      ( k1_tops_1(B_36,D_42) = D_42
      | ~ v3_pre_topc(D_42,B_36)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(u1_struct_0(B_36)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1355,plain,(
    ! [C_201,A_202] :
      ( ~ m1_subset_1(C_201,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202) ) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_1358,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_556,c_1355])).

tff(c_1369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1358])).

tff(c_1477,plain,(
    ! [B_208,D_209] :
      ( k1_tops_1(B_208,D_209) = D_209
      | ~ v3_pre_topc(D_209,B_208)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0(B_208)))
      | ~ l1_pre_topc(B_208) ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1480,plain,
    ( k1_tops_1('#skF_3','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_556,c_1477])).

tff(c_1490,plain,(
    k1_tops_1('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_529,c_1480])).

tff(c_24,plain,(
    ! [A_21,B_25,C_27] :
      ( r1_tarski(k1_tops_1(A_21,B_25),k1_tops_1(A_21,C_27))
      | ~ r1_tarski(B_25,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1521,plain,(
    ! [C_27] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_3',C_27))
      | ~ r1_tarski('#skF_5',C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1490,c_24])).

tff(c_2156,plain,(
    ! [C_245] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_3',C_245))
      | ~ r1_tarski('#skF_5',C_245)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_556,c_1521])).

tff(c_2169,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2156])).

tff(c_2178,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_970,c_2169])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_596,plain,(
    ! [C_133,B_134,A_135] :
      ( r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | ~ r1_tarski(A_135,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_636,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_2'(A_141),B_142)
      | ~ r1_tarski(A_141,B_142)
      | k1_xboole_0 = A_141 ) ),
    inference(resolution,[status(thm)],[c_8,c_596])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_644,plain,(
    ! [B_143,A_144] :
      ( ~ r1_tarski(B_143,'#skF_2'(A_144))
      | ~ r1_tarski(A_144,B_143)
      | k1_xboole_0 = A_144 ) ),
    inference(resolution,[status(thm)],[c_636,c_18])).

tff(c_654,plain,(
    ! [A_144] :
      ( ~ r1_tarski(A_144,k1_xboole_0)
      | k1_xboole_0 = A_144 ) ),
    inference(resolution,[status(thm)],[c_12,c_644])).

tff(c_2191,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2178,c_654])).

tff(c_2211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_2191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.81  
% 4.09/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.81  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.09/1.81  
% 4.09/1.81  %Foreground sorts:
% 4.09/1.81  
% 4.09/1.81  
% 4.09/1.81  %Background operators:
% 4.09/1.81  
% 4.09/1.81  
% 4.09/1.81  %Foreground operators:
% 4.09/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.09/1.81  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.09/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.81  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.09/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.09/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.81  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.09/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.09/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.09/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.81  
% 4.30/1.83  tff(f_133, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 4.30/1.83  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.30/1.83  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.30/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.30/1.83  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.30/1.83  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.30/1.83  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.30/1.83  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.30/1.83  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 4.30/1.83  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.30/1.83  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.30/1.83  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.30/1.83  tff(c_40, plain, (k1_xboole_0!='#skF_5' | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_60, plain, (~v2_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 4.30/1.83  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_136, plain, (![A_79, B_80]: (r1_tarski(k1_tops_1(A_79, B_80), B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.30/1.83  tff(c_141, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_136])).
% 4.30/1.83  tff(c_145, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_141])).
% 4.30/1.83  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_228, plain, (![A_90, B_91]: (v3_pre_topc(k1_tops_1(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.30/1.83  tff(c_233, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_228])).
% 4.30/1.83  tff(c_237, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_233])).
% 4.30/1.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.83  tff(c_89, plain, (![A_65, B_66]: (~r2_hidden('#skF_1'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.83  tff(c_94, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_89])).
% 4.30/1.83  tff(c_74, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.83  tff(c_78, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_74])).
% 4.30/1.83  tff(c_111, plain, (![A_73, C_74, B_75]: (r1_tarski(A_73, C_74) | ~r1_tarski(B_75, C_74) | ~r1_tarski(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.83  tff(c_132, plain, (![A_78]: (r1_tarski(A_78, u1_struct_0('#skF_3')) | ~r1_tarski(A_78, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_111])).
% 4.30/1.83  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.30/1.83  tff(c_208, plain, (![A_88, A_89]: (r1_tarski(A_88, u1_struct_0('#skF_3')) | ~r1_tarski(A_88, A_89) | ~r1_tarski(A_89, '#skF_4'))), inference(resolution, [status(thm)], [c_132, c_10])).
% 4.30/1.83  tff(c_210, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_145, c_208])).
% 4.30/1.83  tff(c_221, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_210])).
% 4.30/1.83  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.30/1.83  tff(c_58, plain, (![C_53]: (v2_tops_1('#skF_4', '#skF_3') | k1_xboole_0=C_53 | ~v3_pre_topc(C_53, '#skF_3') | ~r1_tarski(C_53, '#skF_4') | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_171, plain, (![C_84]: (k1_xboole_0=C_84 | ~v3_pre_topc(C_84, '#skF_3') | ~r1_tarski(C_84, '#skF_4') | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_58])).
% 4.30/1.83  tff(c_448, plain, (![A_111]: (k1_xboole_0=A_111 | ~v3_pre_topc(A_111, '#skF_3') | ~r1_tarski(A_111, '#skF_4') | ~r1_tarski(A_111, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_171])).
% 4.30/1.83  tff(c_459, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski(k1_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_221, c_448])).
% 4.30/1.83  tff(c_478, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_237, c_459])).
% 4.30/1.83  tff(c_512, plain, (![B_113, A_114]: (v2_tops_1(B_113, A_114) | k1_tops_1(A_114, B_113)!=k1_xboole_0 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.30/1.83  tff(c_519, plain, (v2_tops_1('#skF_4', '#skF_3') | k1_tops_1('#skF_3', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_512])).
% 4.30/1.83  tff(c_523, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_478, c_519])).
% 4.30/1.83  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_523])).
% 4.30/1.83  tff(c_526, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 4.30/1.83  tff(c_527, plain, (v2_tops_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 4.30/1.83  tff(c_44, plain, (r1_tarski('#skF_5', '#skF_4') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_532, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_44])).
% 4.30/1.83  tff(c_953, plain, (![A_164, B_165]: (k1_tops_1(A_164, B_165)=k1_xboole_0 | ~v2_tops_1(B_165, A_164) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.30/1.83  tff(c_963, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0 | ~v2_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_953])).
% 4.30/1.83  tff(c_970, plain, (k1_tops_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_527, c_963])).
% 4.30/1.83  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_556, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_46])).
% 4.30/1.83  tff(c_42, plain, (v3_pre_topc('#skF_5', '#skF_3') | ~v2_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.30/1.83  tff(c_529, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_42])).
% 4.30/1.83  tff(c_28, plain, (![B_36, D_42, C_40, A_28]: (k1_tops_1(B_36, D_42)=D_42 | ~v3_pre_topc(D_42, B_36) | ~m1_subset_1(D_42, k1_zfmisc_1(u1_struct_0(B_36))) | ~m1_subset_1(C_40, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.30/1.83  tff(c_1355, plain, (![C_201, A_202]: (~m1_subset_1(C_201, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202))), inference(splitLeft, [status(thm)], [c_28])).
% 4.30/1.83  tff(c_1358, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_556, c_1355])).
% 4.30/1.83  tff(c_1369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1358])).
% 4.30/1.83  tff(c_1477, plain, (![B_208, D_209]: (k1_tops_1(B_208, D_209)=D_209 | ~v3_pre_topc(D_209, B_208) | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0(B_208))) | ~l1_pre_topc(B_208))), inference(splitRight, [status(thm)], [c_28])).
% 4.30/1.83  tff(c_1480, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_556, c_1477])).
% 4.30/1.83  tff(c_1490, plain, (k1_tops_1('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_529, c_1480])).
% 4.30/1.83  tff(c_24, plain, (![A_21, B_25, C_27]: (r1_tarski(k1_tops_1(A_21, B_25), k1_tops_1(A_21, C_27)) | ~r1_tarski(B_25, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.30/1.83  tff(c_1521, plain, (![C_27]: (r1_tarski('#skF_5', k1_tops_1('#skF_3', C_27)) | ~r1_tarski('#skF_5', C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1490, c_24])).
% 4.30/1.83  tff(c_2156, plain, (![C_245]: (r1_tarski('#skF_5', k1_tops_1('#skF_3', C_245)) | ~r1_tarski('#skF_5', C_245) | ~m1_subset_1(C_245, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_556, c_1521])).
% 4.30/1.83  tff(c_2169, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_2156])).
% 4.30/1.83  tff(c_2178, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_532, c_970, c_2169])).
% 4.30/1.83  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.30/1.83  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.30/1.83  tff(c_596, plain, (![C_133, B_134, A_135]: (r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | ~r1_tarski(A_135, B_134))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.30/1.83  tff(c_636, plain, (![A_141, B_142]: (r2_hidden('#skF_2'(A_141), B_142) | ~r1_tarski(A_141, B_142) | k1_xboole_0=A_141)), inference(resolution, [status(thm)], [c_8, c_596])).
% 4.30/1.83  tff(c_18, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.30/1.83  tff(c_644, plain, (![B_143, A_144]: (~r1_tarski(B_143, '#skF_2'(A_144)) | ~r1_tarski(A_144, B_143) | k1_xboole_0=A_144)), inference(resolution, [status(thm)], [c_636, c_18])).
% 4.30/1.83  tff(c_654, plain, (![A_144]: (~r1_tarski(A_144, k1_xboole_0) | k1_xboole_0=A_144)), inference(resolution, [status(thm)], [c_12, c_644])).
% 4.30/1.83  tff(c_2191, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2178, c_654])).
% 4.30/1.83  tff(c_2211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_2191])).
% 4.30/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.83  
% 4.30/1.83  Inference rules
% 4.30/1.83  ----------------------
% 4.30/1.83  #Ref     : 0
% 4.30/1.83  #Sup     : 429
% 4.30/1.83  #Fact    : 0
% 4.30/1.83  #Define  : 0
% 4.30/1.83  #Split   : 12
% 4.30/1.83  #Chain   : 0
% 4.30/1.83  #Close   : 0
% 4.30/1.83  
% 4.30/1.83  Ordering : KBO
% 4.30/1.83  
% 4.30/1.83  Simplification rules
% 4.30/1.83  ----------------------
% 4.30/1.83  #Subsume      : 118
% 4.30/1.83  #Demod        : 333
% 4.30/1.83  #Tautology    : 143
% 4.30/1.83  #SimpNegUnit  : 15
% 4.30/1.83  #BackRed      : 24
% 4.30/1.83  
% 4.30/1.83  #Partial instantiations: 0
% 4.30/1.83  #Strategies tried      : 1
% 4.30/1.83  
% 4.30/1.83  Timing (in seconds)
% 4.30/1.83  ----------------------
% 4.30/1.83  Preprocessing        : 0.34
% 4.30/1.83  Parsing              : 0.19
% 4.30/1.83  CNF conversion       : 0.03
% 4.30/1.83  Main loop            : 0.65
% 4.30/1.83  Inferencing          : 0.22
% 4.30/1.83  Reduction            : 0.20
% 4.30/1.83  Demodulation         : 0.14
% 4.30/1.83  BG Simplification    : 0.03
% 4.30/1.83  Subsumption          : 0.14
% 4.30/1.83  Abstraction          : 0.03
% 4.30/1.83  MUC search           : 0.00
% 4.30/1.83  Cooper               : 0.00
% 4.30/1.83  Total                : 1.03
% 4.30/1.83  Index Insertion      : 0.00
% 4.30/1.83  Index Deletion       : 0.00
% 4.30/1.83  Index Matching       : 0.00
% 4.30/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
