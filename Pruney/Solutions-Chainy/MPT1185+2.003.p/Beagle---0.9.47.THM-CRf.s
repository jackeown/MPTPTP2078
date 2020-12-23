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
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 463 expanded)
%              Number of leaves         :   42 ( 175 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 (1405 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r2_hidden > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r3_orders_1,type,(
    r3_orders_1: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( v6_orders_2(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => r3_orders_1(u1_orders_2(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_orders_2)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_106,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r8_relat_2(C,A)
          & r1_tarski(B,A) )
       => r8_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_orders_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r4_relat_2(C,A)
          & r1_tarski(B,A) )
       => r4_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_orders_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_orders_1)).

tff(c_58,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_16,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_460,plain,(
    ! [A_144] :
      ( m1_subset_1(u1_orders_2(A_144),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_144),u1_struct_0(A_144))))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [B_16,A_14] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_467,plain,(
    ! [A_144] :
      ( v1_relat_1(u1_orders_2(A_144))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_144),u1_struct_0(A_144)))
      | ~ l1_orders_2(A_144) ) ),
    inference(resolution,[status(thm)],[c_460,c_14])).

tff(c_472,plain,(
    ! [A_144] :
      ( v1_relat_1(u1_orders_2(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_467])).

tff(c_56,plain,(
    v6_orders_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_500,plain,(
    ! [A_157,B_158] :
      ( r7_relat_2(u1_orders_2(A_157),B_158)
      | ~ v6_orders_2(B_158,A_157)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | ~ l1_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_503,plain,
    ( r7_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v6_orders_2('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_500])).

tff(c_506,plain,(
    r7_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_503])).

tff(c_44,plain,(
    ! [B_29,A_28] :
      ( r6_relat_2(B_29,A_28)
      | ~ r7_relat_2(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_513,plain,
    ( r6_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_506,c_44])).

tff(c_515,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_518,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_472,c_515])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_518])).

tff(c_524,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_28,plain,(
    ! [A_23] :
      ( r4_relat_2(u1_orders_2(A_23),u1_struct_0(A_23))
      | ~ v5_orders_2(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ~ r3_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_149,plain,(
    ! [A_77] :
      ( m1_subset_1(u1_orders_2(A_77),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_77),u1_struct_0(A_77))))
      | ~ l1_orders_2(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_156,plain,(
    ! [A_77] :
      ( v1_relat_1(u1_orders_2(A_77))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_77),u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77) ) ),
    inference(resolution,[status(thm)],[c_149,c_14])).

tff(c_161,plain,(
    ! [A_77] :
      ( v1_relat_1(u1_orders_2(A_77))
      | ~ l1_orders_2(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_156])).

tff(c_62,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_24,plain,(
    ! [A_22] :
      ( r8_relat_2(u1_orders_2(A_22),u1_struct_0(A_22))
      | ~ v4_orders_2(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_112,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_68,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_112])).

tff(c_116,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_126,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_75,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(A_74,B_75)
      | v1_xboole_0(B_75)
      | ~ m1_subset_1('#skF_1'(A_74,B_75),B_75) ) ),
    inference(resolution,[status(thm)],[c_75,c_4])).

tff(c_135,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_74,u1_struct_0('#skF_2')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_129,c_131])).

tff(c_139,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,u1_struct_0('#skF_2'))
      | ~ r2_hidden('#skF_1'(A_76,u1_struct_0('#skF_2')),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_135])).

tff(c_147,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_163,plain,(
    ! [C_79,B_80,A_81] :
      ( r8_relat_2(C_79,B_80)
      | ~ r1_tarski(B_80,A_81)
      | ~ r8_relat_2(C_79,A_81)
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_170,plain,(
    ! [C_82] :
      ( r8_relat_2(C_82,'#skF_3')
      | ~ r8_relat_2(C_82,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_147,c_163])).

tff(c_174,plain,
    ( r8_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_181,plain,
    ( r8_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_174])).

tff(c_184,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_187,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_161,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_187])).

tff(c_193,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_344,plain,(
    ! [A_112,B_113] :
      ( r7_relat_2(u1_orders_2(A_112),B_113)
      | ~ v6_orders_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_orders_2(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_347,plain,
    ( r7_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v6_orders_2('#skF_3','#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_344])).

tff(c_350,plain,(
    r7_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_347])).

tff(c_46,plain,(
    ! [B_29,A_28] :
      ( r1_relat_2(B_29,A_28)
      | ~ r7_relat_2(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_356,plain,
    ( r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_350,c_46])).

tff(c_362,plain,(
    r1_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_356])).

tff(c_194,plain,(
    ! [C_83,B_84,A_85] :
      ( r4_relat_2(C_83,B_84)
      | ~ r1_tarski(B_84,A_85)
      | ~ r4_relat_2(C_83,A_85)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_201,plain,(
    ! [C_86] :
      ( r4_relat_2(C_86,'#skF_3')
      | ~ r4_relat_2(C_86,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_147,c_194])).

tff(c_205,plain,
    ( r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v5_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_201])).

tff(c_212,plain,(
    r4_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_193,c_205])).

tff(c_353,plain,
    ( r6_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_350,c_44])).

tff(c_359,plain,(
    r6_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_353])).

tff(c_192,plain,(
    r8_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_385,plain,(
    ! [A_124,B_125] :
      ( r3_orders_1(A_124,B_125)
      | ~ r6_relat_2(A_124,B_125)
      | ~ r4_relat_2(A_124,B_125)
      | ~ r8_relat_2(A_124,B_125)
      | ~ r1_relat_2(A_124,B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_391,plain,
    ( r3_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r6_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_192,c_385])).

tff(c_403,plain,(
    r3_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_362,c_212,c_359,c_391])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_403])).

tff(c_408,plain,(
    ! [A_126] : ~ r2_hidden(A_126,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_417,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_408])).

tff(c_445,plain,(
    ! [C_137,B_138,A_139] :
      ( r4_relat_2(C_137,B_138)
      | ~ r1_tarski(B_138,A_139)
      | ~ r4_relat_2(C_137,A_139)
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_452,plain,(
    ! [C_140,B_141] :
      ( r4_relat_2(C_140,'#skF_3')
      | ~ r4_relat_2(C_140,B_141)
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_417,c_445])).

tff(c_457,plain,(
    ! [A_23] :
      ( r4_relat_2(u1_orders_2(A_23),'#skF_3')
      | ~ v1_relat_1(u1_orders_2(A_23))
      | ~ v5_orders_2(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(resolution,[status(thm)],[c_28,c_452])).

tff(c_514,plain,
    ( r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(resolution,[status(thm)],[c_506,c_46])).

tff(c_525,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_525])).

tff(c_528,plain,(
    r1_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_523,plain,(
    r6_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_478,plain,(
    ! [C_147,B_148,A_149] :
      ( r8_relat_2(C_147,B_148)
      | ~ r1_tarski(B_148,A_149)
      | ~ r8_relat_2(C_147,A_149)
      | ~ v1_relat_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_485,plain,(
    ! [C_150,B_151] :
      ( r8_relat_2(C_150,'#skF_3')
      | ~ r8_relat_2(C_150,B_151)
      | ~ v1_relat_1(C_150) ) ),
    inference(resolution,[status(thm)],[c_417,c_478])).

tff(c_490,plain,(
    ! [A_22] :
      ( r8_relat_2(u1_orders_2(A_22),'#skF_3')
      | ~ v1_relat_1(u1_orders_2(A_22))
      | ~ v4_orders_2(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(resolution,[status(thm)],[c_24,c_485])).

tff(c_583,plain,(
    ! [A_177,B_178] :
      ( r3_orders_1(A_177,B_178)
      | ~ r6_relat_2(A_177,B_178)
      | ~ r4_relat_2(A_177,B_178)
      | ~ r8_relat_2(A_177,B_178)
      | ~ r1_relat_2(A_177,B_178)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_596,plain,(
    ! [A_179] :
      ( r3_orders_1(u1_orders_2(A_179),'#skF_3')
      | ~ r6_relat_2(u1_orders_2(A_179),'#skF_3')
      | ~ r4_relat_2(u1_orders_2(A_179),'#skF_3')
      | ~ r1_relat_2(u1_orders_2(A_179),'#skF_3')
      | ~ v1_relat_1(u1_orders_2(A_179))
      | ~ v4_orders_2(A_179)
      | ~ l1_orders_2(A_179) ) ),
    inference(resolution,[status(thm)],[c_490,c_583])).

tff(c_599,plain,
    ( r3_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r4_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r1_relat_2(u1_orders_2('#skF_2'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_523,c_596])).

tff(c_605,plain,
    ( r3_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r4_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_524,c_528,c_599])).

tff(c_606,plain,(
    ~ r4_relat_2(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_605])).

tff(c_610,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v5_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_457,c_606])).

tff(c_617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_524,c_610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.44  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r2_hidden > r1_tarski > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.44  
% 2.89/1.44  %Foreground sorts:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Background operators:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Foreground operators:
% 2.89/1.44  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 2.89/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.89/1.44  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.89/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.44  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.89/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.44  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.89/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.89/1.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.89/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.44  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.44  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.89/1.44  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.89/1.44  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.89/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.44  
% 3.23/1.46  tff(f_141, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => r3_orders_1(u1_orders_2(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_orders_2)).
% 3.23/1.46  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.23/1.46  tff(f_98, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.23/1.46  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.23/1.46  tff(f_69, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_orders_2)).
% 3.23/1.46  tff(f_106, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_orders_1)).
% 3.23/1.46  tff(f_81, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_orders_2)).
% 3.23/1.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.46  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (v4_orders_2(A) <=> r8_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_orders_2)).
% 3.23/1.46  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.23/1.46  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.23/1.46  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.23/1.46  tff(f_122, axiom, (![A, B, C]: (v1_relat_1(C) => ((r8_relat_2(C, A) & r1_tarski(B, A)) => r8_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_orders_1)).
% 3.23/1.46  tff(f_114, axiom, (![A, B, C]: (v1_relat_1(C) => ((r4_relat_2(C, A) & r1_tarski(B, A)) => r4_relat_2(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_orders_1)).
% 3.23/1.46  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_orders_1)).
% 3.23/1.46  tff(c_58, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_60, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_16, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.46  tff(c_460, plain, (![A_144]: (m1_subset_1(u1_orders_2(A_144), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_144), u1_struct_0(A_144)))) | ~l1_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.46  tff(c_14, plain, (![B_16, A_14]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.23/1.46  tff(c_467, plain, (![A_144]: (v1_relat_1(u1_orders_2(A_144)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_144), u1_struct_0(A_144))) | ~l1_orders_2(A_144))), inference(resolution, [status(thm)], [c_460, c_14])).
% 3.23/1.46  tff(c_472, plain, (![A_144]: (v1_relat_1(u1_orders_2(A_144)) | ~l1_orders_2(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_467])).
% 3.23/1.46  tff(c_56, plain, (v6_orders_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_500, plain, (![A_157, B_158]: (r7_relat_2(u1_orders_2(A_157), B_158) | ~v6_orders_2(B_158, A_157) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | ~l1_orders_2(A_157))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.46  tff(c_503, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v6_orders_2('#skF_3', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_54, c_500])).
% 3.23/1.46  tff(c_506, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_503])).
% 3.23/1.46  tff(c_44, plain, (![B_29, A_28]: (r6_relat_2(B_29, A_28) | ~r7_relat_2(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.23/1.46  tff(c_513, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_506, c_44])).
% 3.23/1.46  tff(c_515, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_513])).
% 3.23/1.46  tff(c_518, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_472, c_515])).
% 3.23/1.46  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_518])).
% 3.23/1.46  tff(c_524, plain, (v1_relat_1(u1_orders_2('#skF_2'))), inference(splitRight, [status(thm)], [c_513])).
% 3.23/1.46  tff(c_28, plain, (![A_23]: (r4_relat_2(u1_orders_2(A_23), u1_struct_0(A_23)) | ~v5_orders_2(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.23/1.46  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.46  tff(c_52, plain, (~r3_orders_1(u1_orders_2('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_149, plain, (![A_77]: (m1_subset_1(u1_orders_2(A_77), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_77), u1_struct_0(A_77)))) | ~l1_orders_2(A_77))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.23/1.46  tff(c_156, plain, (![A_77]: (v1_relat_1(u1_orders_2(A_77)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_77), u1_struct_0(A_77))) | ~l1_orders_2(A_77))), inference(resolution, [status(thm)], [c_149, c_14])).
% 3.23/1.46  tff(c_161, plain, (![A_77]: (v1_relat_1(u1_orders_2(A_77)) | ~l1_orders_2(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_156])).
% 3.23/1.46  tff(c_62, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.23/1.46  tff(c_24, plain, (![A_22]: (r8_relat_2(u1_orders_2(A_22), u1_struct_0(A_22)) | ~v4_orders_2(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.46  tff(c_112, plain, (![C_66, B_67, A_68]: (~v1_xboole_0(C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.23/1.46  tff(c_115, plain, (![A_68]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_68, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_112])).
% 3.23/1.46  tff(c_116, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.23/1.46  tff(c_126, plain, (![A_70, C_71, B_72]: (m1_subset_1(A_70, C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.46  tff(c_129, plain, (![A_70]: (m1_subset_1(A_70, u1_struct_0('#skF_2')) | ~r2_hidden(A_70, '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.23/1.46  tff(c_75, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | v1_xboole_0(B_44) | ~m1_subset_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.46  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.46  tff(c_131, plain, (![A_74, B_75]: (r1_tarski(A_74, B_75) | v1_xboole_0(B_75) | ~m1_subset_1('#skF_1'(A_74, B_75), B_75))), inference(resolution, [status(thm)], [c_75, c_4])).
% 3.23/1.46  tff(c_135, plain, (![A_74]: (r1_tarski(A_74, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_74, u1_struct_0('#skF_2')), '#skF_3'))), inference(resolution, [status(thm)], [c_129, c_131])).
% 3.23/1.46  tff(c_139, plain, (![A_76]: (r1_tarski(A_76, u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(A_76, u1_struct_0('#skF_2')), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_116, c_135])).
% 3.23/1.46  tff(c_147, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_139])).
% 3.23/1.46  tff(c_163, plain, (![C_79, B_80, A_81]: (r8_relat_2(C_79, B_80) | ~r1_tarski(B_80, A_81) | ~r8_relat_2(C_79, A_81) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.23/1.46  tff(c_170, plain, (![C_82]: (r8_relat_2(C_82, '#skF_3') | ~r8_relat_2(C_82, u1_struct_0('#skF_2')) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_147, c_163])).
% 3.23/1.46  tff(c_174, plain, (r8_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | ~v4_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_24, c_170])).
% 3.23/1.46  tff(c_181, plain, (r8_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_174])).
% 3.23/1.46  tff(c_184, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_181])).
% 3.23/1.46  tff(c_187, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_161, c_184])).
% 3.23/1.46  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_187])).
% 3.23/1.46  tff(c_193, plain, (v1_relat_1(u1_orders_2('#skF_2'))), inference(splitRight, [status(thm)], [c_181])).
% 3.23/1.46  tff(c_344, plain, (![A_112, B_113]: (r7_relat_2(u1_orders_2(A_112), B_113) | ~v6_orders_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_orders_2(A_112))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.46  tff(c_347, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v6_orders_2('#skF_3', '#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_54, c_344])).
% 3.23/1.46  tff(c_350, plain, (r7_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_347])).
% 3.23/1.46  tff(c_46, plain, (![B_29, A_28]: (r1_relat_2(B_29, A_28) | ~r7_relat_2(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.23/1.46  tff(c_356, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_350, c_46])).
% 3.23/1.46  tff(c_362, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_356])).
% 3.23/1.46  tff(c_194, plain, (![C_83, B_84, A_85]: (r4_relat_2(C_83, B_84) | ~r1_tarski(B_84, A_85) | ~r4_relat_2(C_83, A_85) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.46  tff(c_201, plain, (![C_86]: (r4_relat_2(C_86, '#skF_3') | ~r4_relat_2(C_86, u1_struct_0('#skF_2')) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_147, c_194])).
% 3.23/1.46  tff(c_205, plain, (r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | ~v5_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_28, c_201])).
% 3.23/1.46  tff(c_212, plain, (r4_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_193, c_205])).
% 3.23/1.46  tff(c_353, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_350, c_44])).
% 3.23/1.46  tff(c_359, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_353])).
% 3.23/1.46  tff(c_192, plain, (r8_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_181])).
% 3.23/1.46  tff(c_385, plain, (![A_124, B_125]: (r3_orders_1(A_124, B_125) | ~r6_relat_2(A_124, B_125) | ~r4_relat_2(A_124, B_125) | ~r8_relat_2(A_124, B_125) | ~r1_relat_2(A_124, B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.23/1.46  tff(c_391, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3') | ~r6_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_192, c_385])).
% 3.23/1.46  tff(c_403, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_362, c_212, c_359, c_391])).
% 3.23/1.46  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_403])).
% 3.23/1.46  tff(c_408, plain, (![A_126]: (~r2_hidden(A_126, '#skF_3'))), inference(splitRight, [status(thm)], [c_115])).
% 3.23/1.46  tff(c_417, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_408])).
% 3.23/1.46  tff(c_445, plain, (![C_137, B_138, A_139]: (r4_relat_2(C_137, B_138) | ~r1_tarski(B_138, A_139) | ~r4_relat_2(C_137, A_139) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.23/1.46  tff(c_452, plain, (![C_140, B_141]: (r4_relat_2(C_140, '#skF_3') | ~r4_relat_2(C_140, B_141) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_417, c_445])).
% 3.23/1.46  tff(c_457, plain, (![A_23]: (r4_relat_2(u1_orders_2(A_23), '#skF_3') | ~v1_relat_1(u1_orders_2(A_23)) | ~v5_orders_2(A_23) | ~l1_orders_2(A_23))), inference(resolution, [status(thm)], [c_28, c_452])).
% 3.23/1.46  tff(c_514, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_506, c_46])).
% 3.23/1.46  tff(c_525, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(splitLeft, [status(thm)], [c_514])).
% 3.23/1.46  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_524, c_525])).
% 3.23/1.46  tff(c_528, plain, (r1_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_514])).
% 3.23/1.46  tff(c_523, plain, (r6_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_513])).
% 3.23/1.46  tff(c_478, plain, (![C_147, B_148, A_149]: (r8_relat_2(C_147, B_148) | ~r1_tarski(B_148, A_149) | ~r8_relat_2(C_147, A_149) | ~v1_relat_1(C_147))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.23/1.46  tff(c_485, plain, (![C_150, B_151]: (r8_relat_2(C_150, '#skF_3') | ~r8_relat_2(C_150, B_151) | ~v1_relat_1(C_150))), inference(resolution, [status(thm)], [c_417, c_478])).
% 3.23/1.46  tff(c_490, plain, (![A_22]: (r8_relat_2(u1_orders_2(A_22), '#skF_3') | ~v1_relat_1(u1_orders_2(A_22)) | ~v4_orders_2(A_22) | ~l1_orders_2(A_22))), inference(resolution, [status(thm)], [c_24, c_485])).
% 3.23/1.46  tff(c_583, plain, (![A_177, B_178]: (r3_orders_1(A_177, B_178) | ~r6_relat_2(A_177, B_178) | ~r4_relat_2(A_177, B_178) | ~r8_relat_2(A_177, B_178) | ~r1_relat_2(A_177, B_178) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.23/1.46  tff(c_596, plain, (![A_179]: (r3_orders_1(u1_orders_2(A_179), '#skF_3') | ~r6_relat_2(u1_orders_2(A_179), '#skF_3') | ~r4_relat_2(u1_orders_2(A_179), '#skF_3') | ~r1_relat_2(u1_orders_2(A_179), '#skF_3') | ~v1_relat_1(u1_orders_2(A_179)) | ~v4_orders_2(A_179) | ~l1_orders_2(A_179))), inference(resolution, [status(thm)], [c_490, c_583])).
% 3.23/1.46  tff(c_599, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3') | ~r4_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~r1_relat_2(u1_orders_2('#skF_2'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | ~v4_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_523, c_596])).
% 3.23/1.46  tff(c_605, plain, (r3_orders_1(u1_orders_2('#skF_2'), '#skF_3') | ~r4_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_524, c_528, c_599])).
% 3.23/1.46  tff(c_606, plain, (~r4_relat_2(u1_orders_2('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_605])).
% 3.23/1.46  tff(c_610, plain, (~v1_relat_1(u1_orders_2('#skF_2')) | ~v5_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_457, c_606])).
% 3.23/1.46  tff(c_617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_524, c_610])).
% 3.23/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.46  
% 3.23/1.46  Inference rules
% 3.23/1.46  ----------------------
% 3.23/1.46  #Ref     : 0
% 3.23/1.46  #Sup     : 104
% 3.23/1.46  #Fact    : 0
% 3.23/1.46  #Define  : 0
% 3.23/1.46  #Split   : 9
% 3.23/1.46  #Chain   : 0
% 3.23/1.46  #Close   : 0
% 3.23/1.46  
% 3.23/1.46  Ordering : KBO
% 3.23/1.46  
% 3.23/1.46  Simplification rules
% 3.23/1.46  ----------------------
% 3.23/1.46  #Subsume      : 11
% 3.23/1.46  #Demod        : 53
% 3.23/1.46  #Tautology    : 25
% 3.23/1.46  #SimpNegUnit  : 4
% 3.23/1.46  #BackRed      : 0
% 3.23/1.46  
% 3.23/1.46  #Partial instantiations: 0
% 3.23/1.46  #Strategies tried      : 1
% 3.23/1.46  
% 3.23/1.46  Timing (in seconds)
% 3.23/1.46  ----------------------
% 3.23/1.47  Preprocessing        : 0.31
% 3.23/1.47  Parsing              : 0.17
% 3.23/1.47  CNF conversion       : 0.02
% 3.23/1.47  Main loop            : 0.37
% 3.23/1.47  Inferencing          : 0.15
% 3.23/1.47  Reduction            : 0.10
% 3.23/1.47  Demodulation         : 0.06
% 3.23/1.47  BG Simplification    : 0.02
% 3.23/1.47  Subsumption          : 0.07
% 3.23/1.47  Abstraction          : 0.01
% 3.23/1.47  MUC search           : 0.00
% 3.23/1.47  Cooper               : 0.00
% 3.23/1.47  Total                : 0.73
% 3.23/1.47  Index Insertion      : 0.00
% 3.23/1.47  Index Deletion       : 0.00
% 3.23/1.47  Index Matching       : 0.00
% 3.23/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
