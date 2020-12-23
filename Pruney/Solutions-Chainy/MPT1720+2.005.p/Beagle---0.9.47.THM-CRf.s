%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:42 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 118 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  252 ( 689 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_10,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_pre_topc(k1_tsep_1(A_22,B_23,C_24),A_22)
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    ! [B_45,A_46] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_64])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_77,plain,(
    ! [B_47,A_48] :
      ( v2_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_95,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_107,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_95])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24] :
      ( v1_pre_topc(k1_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_187,plain,(
    ! [A_81,B_82,C_83] :
      ( u1_struct_0(k1_tsep_1(A_81,B_82,C_83)) = k2_xboole_0(u1_struct_0(B_82),u1_struct_0(C_83))
      | ~ m1_pre_topc(k1_tsep_1(A_81,B_82,C_83),A_81)
      | ~ v1_pre_topc(k1_tsep_1(A_81,B_82,C_83))
      | v2_struct_0(k1_tsep_1(A_81,B_82,C_83))
      | ~ m1_pre_topc(C_83,A_81)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_82,A_81)
      | v2_struct_0(B_82)
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_195,plain,(
    ! [A_88,B_89,C_90] :
      ( u1_struct_0(k1_tsep_1(A_88,B_89,C_90)) = k2_xboole_0(u1_struct_0(B_89),u1_struct_0(C_90))
      | ~ v1_pre_topc(k1_tsep_1(A_88,B_89,C_90))
      | v2_struct_0(k1_tsep_1(A_88,B_89,C_90))
      | ~ m1_pre_topc(C_90,A_88)
      | v2_struct_0(C_90)
      | ~ m1_pre_topc(B_89,A_88)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_10,c_187])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ v2_struct_0(k1_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_265,plain,(
    ! [A_91,B_92,C_93] :
      ( u1_struct_0(k1_tsep_1(A_91,B_92,C_93)) = k2_xboole_0(u1_struct_0(B_92),u1_struct_0(C_93))
      | ~ v1_pre_topc(k1_tsep_1(A_91,B_92,C_93))
      | ~ m1_pre_topc(C_93,A_91)
      | v2_struct_0(C_93)
      | ~ m1_pre_topc(B_92,A_91)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_269,plain,(
    ! [A_94,B_95,C_96] :
      ( u1_struct_0(k1_tsep_1(A_94,B_95,C_96)) = k2_xboole_0(u1_struct_0(B_95),u1_struct_0(C_96))
      | ~ m1_pre_topc(C_96,A_94)
      | v2_struct_0(C_96)
      | ~ m1_pre_topc(B_95,A_94)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_12,c_265])).

tff(c_16,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_116,plain,(
    ! [B_49,C_50,A_51] :
      ( r1_tarski(u1_struct_0(B_49),u1_struct_0(C_50))
      | ~ m1_pre_topc(B_49,C_50)
      | ~ m1_pre_topc(C_50,A_51)
      | ~ m1_pre_topc(B_49,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_129,plain,(
    ! [B_49,A_25] :
      ( r1_tarski(u1_struct_0(B_49),u1_struct_0(A_25))
      | ~ m1_pre_topc(B_49,A_25)
      | ~ v2_pre_topc(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_16,c_116])).

tff(c_335,plain,(
    ! [B_97,C_98,A_99,A_100] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_97),u1_struct_0(C_98)),u1_struct_0(A_99))
      | ~ m1_pre_topc(k1_tsep_1(A_100,B_97,C_98),A_99)
      | ~ v2_pre_topc(A_99)
      | ~ l1_pre_topc(A_99)
      | ~ m1_pre_topc(C_98,A_100)
      | v2_struct_0(C_98)
      | ~ m1_pre_topc(B_97,A_100)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_129])).

tff(c_341,plain,(
    ! [B_23,C_24,A_22] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_23),u1_struct_0(C_24)),u1_struct_0(A_22))
      | ~ v2_pre_topc(A_22)
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_335])).

tff(c_20,plain,(
    ! [B_30,C_32,A_26] :
      ( m1_pre_topc(B_30,C_32)
      | ~ r1_tarski(u1_struct_0(B_30),u1_struct_0(C_32))
      | ~ m1_pre_topc(C_32,A_26)
      | ~ m1_pre_topc(B_30,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_829,plain,(
    ! [C_171,A_167,A_169,C_168,B_170] :
      ( m1_pre_topc(k1_tsep_1(A_167,B_170,C_171),C_168)
      | ~ r1_tarski(k2_xboole_0(u1_struct_0(B_170),u1_struct_0(C_171)),u1_struct_0(C_168))
      | ~ m1_pre_topc(C_168,A_169)
      | ~ m1_pre_topc(k1_tsep_1(A_167,B_170,C_171),A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | ~ m1_pre_topc(C_171,A_167)
      | v2_struct_0(C_171)
      | ~ m1_pre_topc(B_170,A_167)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_20])).

tff(c_880,plain,(
    ! [B_183,C_181,A_182,A_179,A_180] :
      ( m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),A_180)
      | ~ m1_pre_topc(A_180,A_179)
      | ~ m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),A_179)
      | ~ l1_pre_topc(A_179)
      | ~ v2_pre_topc(A_179)
      | ~ m1_pre_topc(C_181,A_182)
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ v2_pre_topc(A_180)
      | ~ m1_pre_topc(C_181,A_180)
      | v2_struct_0(C_181)
      | ~ m1_pre_topc(B_183,A_180)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_341,c_829])).

tff(c_894,plain,(
    ! [A_182,B_183,C_181] :
      ( m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_181,A_182)
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(C_181,'#skF_3')
      | v2_struct_0(C_181)
      | ~ m1_pre_topc(B_183,'#skF_3')
      | v2_struct_0(B_183)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_880])).

tff(c_915,plain,(
    ! [A_182,B_183,C_181] :
      ( m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_182,B_183,C_181),'#skF_1')
      | ~ m1_pre_topc(C_181,A_182)
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(C_181,'#skF_3')
      | v2_struct_0(C_181)
      | ~ m1_pre_topc(B_183,'#skF_3')
      | v2_struct_0(B_183)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_107,c_42,c_40,c_894])).

tff(c_966,plain,(
    ! [A_192,B_193,C_194] :
      ( m1_pre_topc(k1_tsep_1(A_192,B_193,C_194),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_192,B_193,C_194),'#skF_1')
      | ~ m1_pre_topc(C_194,A_192)
      | ~ m1_pre_topc(B_193,A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ m1_pre_topc(C_194,'#skF_3')
      | v2_struct_0(C_194)
      | ~ m1_pre_topc(B_193,'#skF_3')
      | v2_struct_0(B_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_915])).

tff(c_22,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_990,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_966,c_22])).

tff(c_1014,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_40,c_36,c_28,c_990])).

tff(c_1015,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_44,c_1014])).

tff(c_1018,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1015])).

tff(c_1021,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_28,c_1018])).

tff(c_1023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_30,c_1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.79  
% 4.38/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.79  %$ r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.38/1.79  
% 4.38/1.79  %Foreground sorts:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Background operators:
% 4.38/1.79  
% 4.38/1.79  
% 4.38/1.79  %Foreground operators:
% 4.38/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.38/1.79  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.38/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.38/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.38/1.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.38/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.38/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.38/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.38/1.79  
% 4.38/1.81  tff(f_142, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 4.38/1.81  tff(f_92, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 4.38/1.81  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.38/1.81  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.38/1.81  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 4.38/1.81  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.38/1.81  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.38/1.81  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_10, plain, (![A_22, B_23, C_24]: (m1_pre_topc(k1_tsep_1(A_22, B_23, C_24), A_22) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.38/1.81  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_46, plain, (![B_45, A_46]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.38/1.81  tff(c_64, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_46])).
% 4.38/1.81  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_64])).
% 4.38/1.81  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_77, plain, (![B_47, A_48]: (v2_pre_topc(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.38/1.81  tff(c_95, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_77])).
% 4.38/1.81  tff(c_107, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_95])).
% 4.38/1.81  tff(c_12, plain, (![A_22, B_23, C_24]: (v1_pre_topc(k1_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.38/1.81  tff(c_187, plain, (![A_81, B_82, C_83]: (u1_struct_0(k1_tsep_1(A_81, B_82, C_83))=k2_xboole_0(u1_struct_0(B_82), u1_struct_0(C_83)) | ~m1_pre_topc(k1_tsep_1(A_81, B_82, C_83), A_81) | ~v1_pre_topc(k1_tsep_1(A_81, B_82, C_83)) | v2_struct_0(k1_tsep_1(A_81, B_82, C_83)) | ~m1_pre_topc(C_83, A_81) | v2_struct_0(C_83) | ~m1_pre_topc(B_82, A_81) | v2_struct_0(B_82) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.38/1.81  tff(c_195, plain, (![A_88, B_89, C_90]: (u1_struct_0(k1_tsep_1(A_88, B_89, C_90))=k2_xboole_0(u1_struct_0(B_89), u1_struct_0(C_90)) | ~v1_pre_topc(k1_tsep_1(A_88, B_89, C_90)) | v2_struct_0(k1_tsep_1(A_88, B_89, C_90)) | ~m1_pre_topc(C_90, A_88) | v2_struct_0(C_90) | ~m1_pre_topc(B_89, A_88) | v2_struct_0(B_89) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_10, c_187])).
% 4.38/1.81  tff(c_14, plain, (![A_22, B_23, C_24]: (~v2_struct_0(k1_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.38/1.81  tff(c_265, plain, (![A_91, B_92, C_93]: (u1_struct_0(k1_tsep_1(A_91, B_92, C_93))=k2_xboole_0(u1_struct_0(B_92), u1_struct_0(C_93)) | ~v1_pre_topc(k1_tsep_1(A_91, B_92, C_93)) | ~m1_pre_topc(C_93, A_91) | v2_struct_0(C_93) | ~m1_pre_topc(B_92, A_91) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_195, c_14])).
% 4.38/1.81  tff(c_269, plain, (![A_94, B_95, C_96]: (u1_struct_0(k1_tsep_1(A_94, B_95, C_96))=k2_xboole_0(u1_struct_0(B_95), u1_struct_0(C_96)) | ~m1_pre_topc(C_96, A_94) | v2_struct_0(C_96) | ~m1_pre_topc(B_95, A_94) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_12, c_265])).
% 4.38/1.81  tff(c_16, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.38/1.81  tff(c_116, plain, (![B_49, C_50, A_51]: (r1_tarski(u1_struct_0(B_49), u1_struct_0(C_50)) | ~m1_pre_topc(B_49, C_50) | ~m1_pre_topc(C_50, A_51) | ~m1_pre_topc(B_49, A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.38/1.81  tff(c_129, plain, (![B_49, A_25]: (r1_tarski(u1_struct_0(B_49), u1_struct_0(A_25)) | ~m1_pre_topc(B_49, A_25) | ~v2_pre_topc(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_16, c_116])).
% 4.38/1.81  tff(c_335, plain, (![B_97, C_98, A_99, A_100]: (r1_tarski(k2_xboole_0(u1_struct_0(B_97), u1_struct_0(C_98)), u1_struct_0(A_99)) | ~m1_pre_topc(k1_tsep_1(A_100, B_97, C_98), A_99) | ~v2_pre_topc(A_99) | ~l1_pre_topc(A_99) | ~m1_pre_topc(C_98, A_100) | v2_struct_0(C_98) | ~m1_pre_topc(B_97, A_100) | v2_struct_0(B_97) | ~l1_pre_topc(A_100) | v2_struct_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_269, c_129])).
% 4.38/1.81  tff(c_341, plain, (![B_23, C_24, A_22]: (r1_tarski(k2_xboole_0(u1_struct_0(B_23), u1_struct_0(C_24)), u1_struct_0(A_22)) | ~v2_pre_topc(A_22) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_10, c_335])).
% 4.38/1.81  tff(c_20, plain, (![B_30, C_32, A_26]: (m1_pre_topc(B_30, C_32) | ~r1_tarski(u1_struct_0(B_30), u1_struct_0(C_32)) | ~m1_pre_topc(C_32, A_26) | ~m1_pre_topc(B_30, A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.38/1.81  tff(c_829, plain, (![C_171, A_167, A_169, C_168, B_170]: (m1_pre_topc(k1_tsep_1(A_167, B_170, C_171), C_168) | ~r1_tarski(k2_xboole_0(u1_struct_0(B_170), u1_struct_0(C_171)), u1_struct_0(C_168)) | ~m1_pre_topc(C_168, A_169) | ~m1_pre_topc(k1_tsep_1(A_167, B_170, C_171), A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | ~m1_pre_topc(C_171, A_167) | v2_struct_0(C_171) | ~m1_pre_topc(B_170, A_167) | v2_struct_0(B_170) | ~l1_pre_topc(A_167) | v2_struct_0(A_167))), inference(superposition, [status(thm), theory('equality')], [c_269, c_20])).
% 4.38/1.81  tff(c_880, plain, (![B_183, C_181, A_182, A_179, A_180]: (m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), A_180) | ~m1_pre_topc(A_180, A_179) | ~m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), A_179) | ~l1_pre_topc(A_179) | ~v2_pre_topc(A_179) | ~m1_pre_topc(C_181, A_182) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182) | v2_struct_0(A_182) | ~v2_pre_topc(A_180) | ~m1_pre_topc(C_181, A_180) | v2_struct_0(C_181) | ~m1_pre_topc(B_183, A_180) | v2_struct_0(B_183) | ~l1_pre_topc(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_341, c_829])).
% 4.38/1.81  tff(c_894, plain, (![A_182, B_183, C_181]: (m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_181, A_182) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182) | v2_struct_0(A_182) | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(C_181, '#skF_3') | v2_struct_0(C_181) | ~m1_pre_topc(B_183, '#skF_3') | v2_struct_0(B_183) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_880])).
% 4.38/1.81  tff(c_915, plain, (![A_182, B_183, C_181]: (m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_182, B_183, C_181), '#skF_1') | ~m1_pre_topc(C_181, A_182) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(C_181, '#skF_3') | v2_struct_0(C_181) | ~m1_pre_topc(B_183, '#skF_3') | v2_struct_0(B_183) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_107, c_42, c_40, c_894])).
% 4.38/1.81  tff(c_966, plain, (![A_192, B_193, C_194]: (m1_pre_topc(k1_tsep_1(A_192, B_193, C_194), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_192, B_193, C_194), '#skF_1') | ~m1_pre_topc(C_194, A_192) | ~m1_pre_topc(B_193, A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192) | ~m1_pre_topc(C_194, '#skF_3') | v2_struct_0(C_194) | ~m1_pre_topc(B_193, '#skF_3') | v2_struct_0(B_193))), inference(negUnitSimplification, [status(thm)], [c_34, c_915])).
% 4.38/1.81  tff(c_22, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.38/1.81  tff(c_990, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_966, c_22])).
% 4.38/1.81  tff(c_1014, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_40, c_36, c_28, c_990])).
% 4.38/1.81  tff(c_1015, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_44, c_1014])).
% 4.38/1.81  tff(c_1018, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_1015])).
% 4.38/1.81  tff(c_1021, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_28, c_1018])).
% 4.38/1.81  tff(c_1023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_30, c_1021])).
% 4.38/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.81  
% 4.38/1.81  Inference rules
% 4.38/1.81  ----------------------
% 4.38/1.81  #Ref     : 0
% 4.38/1.81  #Sup     : 279
% 4.38/1.81  #Fact    : 0
% 4.38/1.81  #Define  : 0
% 4.38/1.81  #Split   : 0
% 4.38/1.81  #Chain   : 0
% 4.38/1.81  #Close   : 0
% 4.38/1.81  
% 4.38/1.81  Ordering : KBO
% 4.38/1.81  
% 4.38/1.81  Simplification rules
% 4.38/1.81  ----------------------
% 4.38/1.81  #Subsume      : 45
% 4.38/1.81  #Demod        : 86
% 4.38/1.81  #Tautology    : 18
% 4.38/1.81  #SimpNegUnit  : 13
% 4.38/1.81  #BackRed      : 0
% 4.38/1.81  
% 4.38/1.81  #Partial instantiations: 0
% 4.38/1.81  #Strategies tried      : 1
% 4.38/1.81  
% 4.38/1.81  Timing (in seconds)
% 4.38/1.81  ----------------------
% 4.38/1.81  Preprocessing        : 0.31
% 4.38/1.81  Parsing              : 0.17
% 4.38/1.81  CNF conversion       : 0.03
% 4.38/1.81  Main loop            : 0.65
% 4.38/1.81  Inferencing          : 0.24
% 4.38/1.81  Reduction            : 0.16
% 4.57/1.81  Demodulation         : 0.11
% 4.57/1.81  BG Simplification    : 0.03
% 4.57/1.81  Subsumption          : 0.19
% 4.57/1.81  Abstraction          : 0.03
% 4.57/1.81  MUC search           : 0.00
% 4.57/1.81  Cooper               : 0.00
% 4.57/1.81  Total                : 1.00
% 4.57/1.81  Index Insertion      : 0.00
% 4.57/1.81  Index Deletion       : 0.00
% 4.57/1.81  Index Matching       : 0.00
% 4.57/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
