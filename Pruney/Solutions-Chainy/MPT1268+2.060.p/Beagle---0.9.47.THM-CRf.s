%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:55 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 331 expanded)
%              Number of leaves         :   30 ( 120 expanded)
%              Depth                    :   15
%              Number of atoms          :  235 ( 971 expanded)
%              Number of equality atoms :   34 ( 124 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_148,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_61,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_129,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tops_1(A_85,B_86),B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_134,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_129])).

tff(c_141,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_134])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_411,plain,(
    ! [A_111,B_112] :
      ( v3_pre_topc(k1_tops_1(A_111,B_112),A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_419,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_411])).

tff(c_427,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_419])).

tff(c_75,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_90,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_82,c_90])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [C_59] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_59
      | ~ v3_pre_topc(C_59,'#skF_2')
      | ~ r1_tarski(C_59,'#skF_3')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_167,plain,(
    ! [C_90] :
      ( k1_xboole_0 = C_90
      | ~ v3_pre_topc(C_90,'#skF_2')
      | ~ r1_tarski(C_90,'#skF_3')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_58])).

tff(c_457,plain,(
    ! [A_115] :
      ( k1_xboole_0 = A_115
      | ~ v3_pre_topc(A_115,'#skF_2')
      | ~ r1_tarski(A_115,'#skF_3')
      | ~ r1_tarski(A_115,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_167])).

tff(c_494,plain,(
    ! [A_116] :
      ( k1_xboole_0 = A_116
      | ~ v3_pre_topc(A_116,'#skF_2')
      | ~ r1_tarski(A_116,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_95,c_457])).

tff(c_504,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_427,c_494])).

tff(c_514,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_504])).

tff(c_530,plain,(
    ! [B_117,A_118] :
      ( v2_tops_1(B_117,A_118)
      | k1_tops_1(A_118,B_117) != k1_xboole_0
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_541,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | k1_tops_1('#skF_2','#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_530])).

tff(c_550,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_514,c_541])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_550])).

tff(c_553,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_554,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_556,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_42])).

tff(c_46,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_588,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_46])).

tff(c_777,plain,(
    ! [B_156,A_157] :
      ( v2_tops_1(B_156,A_157)
      | k1_tops_1(A_157,B_156) != k1_xboole_0
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_pre_topc(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_784,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_777])).

tff(c_799,plain,
    ( v2_tops_1('#skF_4','#skF_2')
    | k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_784])).

tff(c_805,plain,(
    k1_tops_1('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_799])).

tff(c_44,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_559,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_44])).

tff(c_686,plain,(
    ! [A_149,B_150] :
      ( r1_tarski(k1_tops_1(A_149,B_150),B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_691,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_686])).

tff(c_703,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_691])).

tff(c_573,plain,(
    ! [A_125,B_126] :
      ( r1_tarski(A_125,B_126)
      | ~ m1_subset_1(A_125,k1_zfmisc_1(B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_584,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_573])).

tff(c_593,plain,(
    ! [A_127,C_128,B_129] :
      ( r1_tarski(A_127,C_128)
      | ~ r1_tarski(B_129,C_128)
      | ~ r1_tarski(A_127,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_620,plain,(
    ! [A_134] :
      ( r1_tarski(A_134,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_134,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_584,c_593])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_938,plain,(
    ! [A_169,A_170] :
      ( r1_tarski(A_169,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_169,A_170)
      | ~ r1_tarski(A_170,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_620,c_4])).

tff(c_946,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_703,c_938])).

tff(c_966,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_946])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_722,plain,(
    ! [A_151] :
      ( r1_tarski(k1_tops_1(A_151,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_8,c_686])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_605,plain,(
    ! [A_127,A_6] :
      ( r1_tarski(A_127,A_6)
      | ~ r1_tarski(A_127,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_593])).

tff(c_735,plain,(
    ! [A_152,A_153] :
      ( r1_tarski(k1_tops_1(A_152,k1_xboole_0),A_153)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_722,c_605])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_560,plain,(
    ! [B_120,A_121] :
      ( ~ r1_tarski(B_120,A_121)
      | ~ r2_hidden(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_564,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_560])).

tff(c_751,plain,(
    ! [A_154] :
      ( k1_tops_1(A_154,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_735,c_564])).

tff(c_755,plain,(
    k1_tops_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_751])).

tff(c_1172,plain,(
    ! [A_182,B_183,C_184] :
      ( r1_tarski(k1_tops_1(A_182,B_183),k1_tops_1(A_182,C_184))
      | ~ r1_tarski(B_183,C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1203,plain,(
    ! [B_183] :
      ( r1_tarski(k1_tops_1('#skF_2',B_183),k1_xboole_0)
      | ~ r1_tarski(B_183,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_1172])).

tff(c_1275,plain,(
    ! [B_187] :
      ( r1_tarski(k1_tops_1('#skF_2',B_187),k1_xboole_0)
      | ~ r1_tarski(B_187,k1_xboole_0)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8,c_1203])).

tff(c_1303,plain,(
    ! [A_188] :
      ( r1_tarski(k1_tops_1('#skF_2',A_188),k1_xboole_0)
      | ~ r1_tarski(A_188,k1_xboole_0)
      | ~ r1_tarski(A_188,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1275])).

tff(c_1358,plain,(
    ! [A_190,A_191] :
      ( r1_tarski(k1_tops_1('#skF_2',A_190),A_191)
      | ~ r1_tarski(A_190,k1_xboole_0)
      | ~ r1_tarski(A_190,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1303,c_605])).

tff(c_1444,plain,(
    ! [A_194] :
      ( k1_tops_1('#skF_2',A_194) = k1_xboole_0
      | ~ r1_tarski(A_194,k1_xboole_0)
      | ~ r1_tarski(A_194,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1358,c_564])).

tff(c_1487,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_xboole_0
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_966,c_1444])).

tff(c_1569,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1487])).

tff(c_978,plain,(
    ! [A_171,B_172] :
      ( k1_tops_1(A_171,B_172) = k1_xboole_0
      | ~ v2_tops_1(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_992,plain,
    ( k1_tops_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_978])).

tff(c_1005,plain,(
    k1_tops_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_554,c_992])).

tff(c_1197,plain,(
    ! [B_183] :
      ( r1_tarski(k1_tops_1('#skF_2',B_183),k1_xboole_0)
      | ~ r1_tarski(B_183,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1005,c_1172])).

tff(c_1704,plain,(
    ! [B_205] :
      ( r1_tarski(k1_tops_1('#skF_2',B_205),k1_xboole_0)
      | ~ r1_tarski(B_205,'#skF_3')
      | ~ m1_subset_1(B_205,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1197])).

tff(c_1711,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_588,c_1704])).

tff(c_1726,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_1711])).

tff(c_1728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1569,c_1726])).

tff(c_1730,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1487])).

tff(c_1781,plain,(
    ! [A_206] : r1_tarski(k1_tops_1('#skF_2','#skF_4'),A_206) ),
    inference(resolution,[status(thm)],[c_1730,c_605])).

tff(c_1831,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1781,c_564])).

tff(c_1868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_1831])).

tff(c_1870,plain,(
    k1_tops_1('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_26,plain,(
    ! [B_35,D_41,C_39,A_27] :
      ( k1_tops_1(B_35,D_41) = D_41
      | ~ v3_pre_topc(D_41,B_35)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2489,plain,(
    ! [C_244,A_245] :
      ( ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245) ) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_2496,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_2489])).

tff(c_2511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2496])).

tff(c_2780,plain,(
    ! [B_255,D_256] :
      ( k1_tops_1(B_255,D_256) = D_256
      | ~ v3_pre_topc(D_256,B_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(u1_struct_0(B_255)))
      | ~ l1_pre_topc(B_255) ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2787,plain,
    ( k1_tops_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_588,c_2780])).

tff(c_2802,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_556,c_1870,c_2787])).

tff(c_2804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_553,c_2802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.81  
% 4.42/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.81  %$ v3_pre_topc > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.42/1.81  
% 4.42/1.81  %Foreground sorts:
% 4.42/1.81  
% 4.42/1.81  
% 4.42/1.81  %Background operators:
% 4.42/1.81  
% 4.42/1.81  
% 4.42/1.81  %Foreground operators:
% 4.42/1.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.42/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.81  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.42/1.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.42/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.81  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.42/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.42/1.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.42/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/1.81  
% 4.48/1.83  tff(f_148, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 4.48/1.83  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.48/1.83  tff(f_66, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 4.48/1.83  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.48/1.83  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.48/1.83  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 4.48/1.83  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.48/1.83  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.48/1.83  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.48/1.83  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.48/1.83  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.48/1.83  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 4.48/1.83  tff(c_40, plain, (k1_xboole_0!='#skF_4' | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_61, plain, (~v2_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.48/1.83  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_129, plain, (![A_85, B_86]: (r1_tarski(k1_tops_1(A_85, B_86), B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.83  tff(c_134, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_129])).
% 4.48/1.83  tff(c_141, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_134])).
% 4.48/1.83  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_411, plain, (![A_111, B_112]: (v3_pre_topc(k1_tops_1(A_111, B_112), A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.48/1.83  tff(c_419, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_411])).
% 4.48/1.83  tff(c_427, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_419])).
% 4.48/1.83  tff(c_75, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.48/1.83  tff(c_82, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_75])).
% 4.48/1.83  tff(c_90, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.83  tff(c_95, plain, (![A_70]: (r1_tarski(A_70, u1_struct_0('#skF_2')) | ~r1_tarski(A_70, '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_90])).
% 4.48/1.83  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.48/1.83  tff(c_58, plain, (![C_59]: (v2_tops_1('#skF_3', '#skF_2') | k1_xboole_0=C_59 | ~v3_pre_topc(C_59, '#skF_2') | ~r1_tarski(C_59, '#skF_3') | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_167, plain, (![C_90]: (k1_xboole_0=C_90 | ~v3_pre_topc(C_90, '#skF_2') | ~r1_tarski(C_90, '#skF_3') | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_61, c_58])).
% 4.48/1.83  tff(c_457, plain, (![A_115]: (k1_xboole_0=A_115 | ~v3_pre_topc(A_115, '#skF_2') | ~r1_tarski(A_115, '#skF_3') | ~r1_tarski(A_115, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_167])).
% 4.48/1.83  tff(c_494, plain, (![A_116]: (k1_xboole_0=A_116 | ~v3_pre_topc(A_116, '#skF_2') | ~r1_tarski(A_116, '#skF_3'))), inference(resolution, [status(thm)], [c_95, c_457])).
% 4.48/1.83  tff(c_504, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_427, c_494])).
% 4.48/1.83  tff(c_514, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_141, c_504])).
% 4.48/1.83  tff(c_530, plain, (![B_117, A_118]: (v2_tops_1(B_117, A_118) | k1_tops_1(A_118, B_117)!=k1_xboole_0 | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.48/1.83  tff(c_541, plain, (v2_tops_1('#skF_3', '#skF_2') | k1_tops_1('#skF_2', '#skF_3')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_530])).
% 4.48/1.83  tff(c_550, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_514, c_541])).
% 4.48/1.83  tff(c_552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_550])).
% 4.48/1.83  tff(c_553, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 4.48/1.83  tff(c_554, plain, (v2_tops_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.48/1.83  tff(c_42, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_556, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_42])).
% 4.48/1.83  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_588, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_554, c_46])).
% 4.48/1.83  tff(c_777, plain, (![B_156, A_157]: (v2_tops_1(B_156, A_157) | k1_tops_1(A_157, B_156)!=k1_xboole_0 | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_pre_topc(A_157))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.48/1.83  tff(c_784, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0 | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_588, c_777])).
% 4.48/1.83  tff(c_799, plain, (v2_tops_1('#skF_4', '#skF_2') | k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_784])).
% 4.48/1.83  tff(c_805, plain, (k1_tops_1('#skF_2', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_799])).
% 4.48/1.83  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_3') | ~v2_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.48/1.83  tff(c_559, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_44])).
% 4.48/1.83  tff(c_686, plain, (![A_149, B_150]: (r1_tarski(k1_tops_1(A_149, B_150), B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.48/1.83  tff(c_691, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_588, c_686])).
% 4.48/1.83  tff(c_703, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_691])).
% 4.48/1.83  tff(c_573, plain, (![A_125, B_126]: (r1_tarski(A_125, B_126) | ~m1_subset_1(A_125, k1_zfmisc_1(B_126)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.48/1.83  tff(c_584, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_573])).
% 4.48/1.83  tff(c_593, plain, (![A_127, C_128, B_129]: (r1_tarski(A_127, C_128) | ~r1_tarski(B_129, C_128) | ~r1_tarski(A_127, B_129))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.83  tff(c_620, plain, (![A_134]: (r1_tarski(A_134, u1_struct_0('#skF_2')) | ~r1_tarski(A_134, '#skF_3'))), inference(resolution, [status(thm)], [c_584, c_593])).
% 4.48/1.83  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.48/1.83  tff(c_938, plain, (![A_169, A_170]: (r1_tarski(A_169, u1_struct_0('#skF_2')) | ~r1_tarski(A_169, A_170) | ~r1_tarski(A_170, '#skF_3'))), inference(resolution, [status(thm)], [c_620, c_4])).
% 4.48/1.83  tff(c_946, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_703, c_938])).
% 4.48/1.83  tff(c_966, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_559, c_946])).
% 4.48/1.83  tff(c_8, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.48/1.83  tff(c_722, plain, (![A_151]: (r1_tarski(k1_tops_1(A_151, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_8, c_686])).
% 4.48/1.83  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.48/1.83  tff(c_605, plain, (![A_127, A_6]: (r1_tarski(A_127, A_6) | ~r1_tarski(A_127, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_593])).
% 4.48/1.83  tff(c_735, plain, (![A_152, A_153]: (r1_tarski(k1_tops_1(A_152, k1_xboole_0), A_153) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_722, c_605])).
% 4.48/1.83  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.83  tff(c_560, plain, (![B_120, A_121]: (~r1_tarski(B_120, A_121) | ~r2_hidden(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.48/1.83  tff(c_564, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_560])).
% 4.48/1.83  tff(c_751, plain, (![A_154]: (k1_tops_1(A_154, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_154))), inference(resolution, [status(thm)], [c_735, c_564])).
% 4.48/1.83  tff(c_755, plain, (k1_tops_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_751])).
% 4.48/1.83  tff(c_1172, plain, (![A_182, B_183, C_184]: (r1_tarski(k1_tops_1(A_182, B_183), k1_tops_1(A_182, C_184)) | ~r1_tarski(B_183, C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(u1_struct_0(A_182))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.48/1.83  tff(c_1203, plain, (![B_183]: (r1_tarski(k1_tops_1('#skF_2', B_183), k1_xboole_0) | ~r1_tarski(B_183, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_755, c_1172])).
% 4.48/1.83  tff(c_1275, plain, (![B_187]: (r1_tarski(k1_tops_1('#skF_2', B_187), k1_xboole_0) | ~r1_tarski(B_187, k1_xboole_0) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8, c_1203])).
% 4.48/1.83  tff(c_1303, plain, (![A_188]: (r1_tarski(k1_tops_1('#skF_2', A_188), k1_xboole_0) | ~r1_tarski(A_188, k1_xboole_0) | ~r1_tarski(A_188, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_1275])).
% 4.48/1.83  tff(c_1358, plain, (![A_190, A_191]: (r1_tarski(k1_tops_1('#skF_2', A_190), A_191) | ~r1_tarski(A_190, k1_xboole_0) | ~r1_tarski(A_190, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1303, c_605])).
% 4.48/1.83  tff(c_1444, plain, (![A_194]: (k1_tops_1('#skF_2', A_194)=k1_xboole_0 | ~r1_tarski(A_194, k1_xboole_0) | ~r1_tarski(A_194, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1358, c_564])).
% 4.48/1.83  tff(c_1487, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_xboole_0 | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_966, c_1444])).
% 4.48/1.83  tff(c_1569, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1487])).
% 4.48/1.83  tff(c_978, plain, (![A_171, B_172]: (k1_tops_1(A_171, B_172)=k1_xboole_0 | ~v2_tops_1(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.48/1.83  tff(c_992, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v2_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_978])).
% 4.48/1.83  tff(c_1005, plain, (k1_tops_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_554, c_992])).
% 4.48/1.83  tff(c_1197, plain, (![B_183]: (r1_tarski(k1_tops_1('#skF_2', B_183), k1_xboole_0) | ~r1_tarski(B_183, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1005, c_1172])).
% 4.48/1.83  tff(c_1704, plain, (![B_205]: (r1_tarski(k1_tops_1('#skF_2', B_205), k1_xboole_0) | ~r1_tarski(B_205, '#skF_3') | ~m1_subset_1(B_205, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1197])).
% 4.48/1.83  tff(c_1711, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_588, c_1704])).
% 4.48/1.83  tff(c_1726, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_559, c_1711])).
% 4.48/1.83  tff(c_1728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1569, c_1726])).
% 4.48/1.83  tff(c_1730, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1487])).
% 4.48/1.83  tff(c_1781, plain, (![A_206]: (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), A_206))), inference(resolution, [status(thm)], [c_1730, c_605])).
% 4.48/1.83  tff(c_1831, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1781, c_564])).
% 4.48/1.83  tff(c_1868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_805, c_1831])).
% 4.48/1.83  tff(c_1870, plain, (k1_tops_1('#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_799])).
% 4.48/1.83  tff(c_26, plain, (![B_35, D_41, C_39, A_27]: (k1_tops_1(B_35, D_41)=D_41 | ~v3_pre_topc(D_41, B_35) | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.48/1.83  tff(c_2489, plain, (![C_244, A_245]: (~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245))), inference(splitLeft, [status(thm)], [c_26])).
% 4.48/1.83  tff(c_2496, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_588, c_2489])).
% 4.48/1.83  tff(c_2511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2496])).
% 4.48/1.83  tff(c_2780, plain, (![B_255, D_256]: (k1_tops_1(B_255, D_256)=D_256 | ~v3_pre_topc(D_256, B_255) | ~m1_subset_1(D_256, k1_zfmisc_1(u1_struct_0(B_255))) | ~l1_pre_topc(B_255))), inference(splitRight, [status(thm)], [c_26])).
% 4.48/1.83  tff(c_2787, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4' | ~v3_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_588, c_2780])).
% 4.48/1.83  tff(c_2802, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_556, c_1870, c_2787])).
% 4.48/1.83  tff(c_2804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_553, c_2802])).
% 4.48/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.83  
% 4.48/1.83  Inference rules
% 4.48/1.83  ----------------------
% 4.48/1.83  #Ref     : 0
% 4.48/1.83  #Sup     : 567
% 4.48/1.83  #Fact    : 0
% 4.48/1.83  #Define  : 0
% 4.48/1.83  #Split   : 12
% 4.48/1.83  #Chain   : 0
% 4.48/1.83  #Close   : 0
% 4.48/1.83  
% 4.48/1.83  Ordering : KBO
% 4.48/1.83  
% 4.48/1.83  Simplification rules
% 4.48/1.83  ----------------------
% 4.48/1.83  #Subsume      : 142
% 4.48/1.83  #Demod        : 379
% 4.48/1.83  #Tautology    : 169
% 4.48/1.83  #SimpNegUnit  : 11
% 4.48/1.83  #BackRed      : 10
% 4.48/1.83  
% 4.48/1.84  #Partial instantiations: 0
% 4.48/1.84  #Strategies tried      : 1
% 4.48/1.84  
% 4.48/1.84  Timing (in seconds)
% 4.48/1.84  ----------------------
% 4.48/1.84  Preprocessing        : 0.37
% 4.48/1.84  Parsing              : 0.20
% 4.48/1.84  CNF conversion       : 0.03
% 4.48/1.84  Main loop            : 0.68
% 4.48/1.84  Inferencing          : 0.23
% 4.48/1.84  Reduction            : 0.21
% 4.48/1.84  Demodulation         : 0.14
% 4.48/1.84  BG Simplification    : 0.03
% 4.48/1.84  Subsumption          : 0.15
% 4.48/1.84  Abstraction          : 0.03
% 4.48/1.84  MUC search           : 0.00
% 4.48/1.84  Cooper               : 0.00
% 4.48/1.84  Total                : 1.10
% 4.48/1.84  Index Insertion      : 0.00
% 4.48/1.84  Index Deletion       : 0.00
% 4.48/1.84  Index Matching       : 0.00
% 4.48/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
