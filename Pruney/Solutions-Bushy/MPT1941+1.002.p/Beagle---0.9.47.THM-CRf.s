%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1941+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:42 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 375 expanded)
%              Number of leaves         :   40 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          :  303 (1130 expanded)
%              Number of equality atoms :   90 ( 200 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_partfun1 > r2_hidden > m1_subset_1 > v8_relat_2 > v4_relat_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_2 > v1_orders_2 > l1_pre_topc > l1_orders_2 > k9_yellow_6 > k2_zfmisc_1 > g1_orders_2 > a_2_0_yellow_6 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(a_2_0_yellow_6,type,(
    a_2_0_yellow_6: ( $i * $i ) > $i )).

tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( r2_hidden(A,a_2_0_yellow_6(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & A = D
            & r2_hidden(C,D)
            & v3_pre_topc(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_6)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_44,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k9_yellow_6(A,B) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_yellow_6)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => u1_struct_0(A) = u1_struct_0(k7_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,
    ( r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4')))
    | r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_112,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_70,plain,
    ( r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4')))
    | v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_111,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_810,plain,(
    ! [D_182,B_183,C_184] :
      ( r2_hidden(D_182,a_2_0_yellow_6(B_183,C_184))
      | ~ v3_pre_topc(D_182,B_183)
      | ~ r2_hidden(C_184,D_182)
      | ~ m1_subset_1(D_182,k1_zfmisc_1(u1_struct_0(B_183)))
      | ~ m1_subset_1(C_184,u1_struct_0(B_183))
      | ~ l1_pre_topc(B_183)
      | ~ v2_pre_topc(B_183)
      | v2_struct_0(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_826,plain,(
    ! [C_184] :
      ( r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3',C_184))
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ r2_hidden(C_184,'#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_810])).

tff(c_833,plain,(
    ! [C_184] :
      ( r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3',C_184))
      | ~ r2_hidden(C_184,'#skF_5')
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_111,c_826])).

tff(c_835,plain,(
    ! [C_185] :
      ( r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3',C_185))
      | ~ r2_hidden(C_185,'#skF_5')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_833])).

tff(c_20,plain,(
    ! [A_7] : l1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_7] : v1_orders_2(k2_yellow_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_yellow_1(A_6),k1_zfmisc_1(k2_zfmisc_1(A_6,A_6))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_5] : g1_orders_2(A_5,k1_yellow_1(A_5)) = k2_yellow_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_158,plain,(
    ! [D_72,B_73,C_74,A_75] :
      ( D_72 = B_73
      | g1_orders_2(C_74,D_72) != g1_orders_2(A_75,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_zfmisc_1(A_75,A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_166,plain,(
    ! [A_5,D_72,C_74] :
      ( k1_yellow_1(A_5) = D_72
      | k2_yellow_1(A_5) != g1_orders_2(C_74,D_72)
      | ~ m1_subset_1(k1_yellow_1(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_169,plain,(
    ! [A_76,D_77,C_78] :
      ( k1_yellow_1(A_76) = D_77
      | k2_yellow_1(A_76) != g1_orders_2(C_78,D_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_172,plain,(
    ! [A_1,A_76] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_76)
      | k2_yellow_1(A_76) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_184,plain,(
    ! [A_76] :
      ( u1_orders_2(k2_yellow_1(A_76)) = k1_yellow_1(A_76)
      | ~ v1_orders_2(k2_yellow_1(A_76))
      | ~ l1_orders_2(k2_yellow_1(A_76)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_172])).

tff(c_203,plain,(
    ! [A_87] : u1_orders_2(k2_yellow_1(A_87)) = k1_yellow_1(A_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_184])).

tff(c_209,plain,(
    ! [A_87] :
      ( g1_orders_2(u1_struct_0(k2_yellow_1(A_87)),k1_yellow_1(A_87)) = k2_yellow_1(A_87)
      | ~ v1_orders_2(k2_yellow_1(A_87))
      | ~ l1_orders_2(k2_yellow_1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_243,plain,(
    ! [A_95] : g1_orders_2(u1_struct_0(k2_yellow_1(A_95)),k1_yellow_1(A_95)) = k2_yellow_1(A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_209])).

tff(c_192,plain,(
    ! [C_83,A_84,D_85,B_86] :
      ( C_83 = A_84
      | g1_orders_2(C_83,D_85) != g1_orders_2(A_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_84,A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_200,plain,(
    ! [C_83,A_5,D_85] :
      ( C_83 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_83,D_85)
      | ~ m1_subset_1(k1_yellow_1(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_192])).

tff(c_202,plain,(
    ! [C_83,A_5,D_85] :
      ( C_83 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_83,D_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_200])).

tff(c_249,plain,(
    ! [A_95,A_5] :
      ( u1_struct_0(k2_yellow_1(A_95)) = A_5
      | k2_yellow_1(A_95) != k2_yellow_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_202])).

tff(c_268,plain,(
    ! [A_5] : u1_struct_0(k2_yellow_1(A_5)) = A_5 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_249])).

tff(c_229,plain,(
    ! [A_93,B_94] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_93,B_94))) = k9_yellow_6(A_93,B_94)
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_20] :
      ( u1_struct_0(k7_lattice3(A_20)) = u1_struct_0(A_20)
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [A_93,B_94] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_93,B_94))) = u1_struct_0(k9_yellow_6(A_93,B_94))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_93,B_94)))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_36])).

tff(c_241,plain,(
    ! [A_93,B_94] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_93,B_94))) = u1_struct_0(k9_yellow_6(A_93,B_94))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_235])).

tff(c_412,plain,(
    ! [A_122,B_123] :
      ( u1_struct_0(k9_yellow_6(A_122,B_123)) = a_2_0_yellow_6(A_122,B_123)
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_241])).

tff(c_424,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_412])).

tff(c_431,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_424])).

tff(c_432,plain,(
    u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_431])).

tff(c_64,plain,
    ( ~ v3_pre_topc('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_111,c_64])).

tff(c_434,plain,(
    ~ r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_141])).

tff(c_838,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_835,c_434])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_112,c_838])).

tff(c_855,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_901,plain,(
    ! [D_195,B_196,C_197,A_198] :
      ( D_195 = B_196
      | g1_orders_2(C_197,D_195) != g1_orders_2(A_198,B_196)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_909,plain,(
    ! [A_5,D_195,C_197] :
      ( k1_yellow_1(A_5) = D_195
      | k2_yellow_1(A_5) != g1_orders_2(C_197,D_195)
      | ~ m1_subset_1(k1_yellow_1(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_901])).

tff(c_912,plain,(
    ! [A_199,D_200,C_201] :
      ( k1_yellow_1(A_199) = D_200
      | k2_yellow_1(A_199) != g1_orders_2(C_201,D_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_909])).

tff(c_915,plain,(
    ! [A_1,A_199] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_199)
      | k2_yellow_1(A_199) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_912])).

tff(c_927,plain,(
    ! [A_199] :
      ( u1_orders_2(k2_yellow_1(A_199)) = k1_yellow_1(A_199)
      | ~ v1_orders_2(k2_yellow_1(A_199))
      | ~ l1_orders_2(k2_yellow_1(A_199)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_915])).

tff(c_931,plain,(
    ! [A_206] : u1_orders_2(k2_yellow_1(A_206)) = k1_yellow_1(A_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_927])).

tff(c_937,plain,(
    ! [A_206] :
      ( g1_orders_2(u1_struct_0(k2_yellow_1(A_206)),k1_yellow_1(A_206)) = k2_yellow_1(A_206)
      | ~ v1_orders_2(k2_yellow_1(A_206))
      | ~ l1_orders_2(k2_yellow_1(A_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_2])).

tff(c_943,plain,(
    ! [A_206] : g1_orders_2(u1_struct_0(k2_yellow_1(A_206)),k1_yellow_1(A_206)) = k2_yellow_1(A_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_937])).

tff(c_965,plain,(
    ! [C_208,A_209,D_210,B_211] :
      ( C_208 = A_209
      | g1_orders_2(C_208,D_210) != g1_orders_2(A_209,B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_977,plain,(
    ! [C_208,A_5,D_210] :
      ( C_208 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_208,D_210)
      | ~ m1_subset_1(k1_yellow_1(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_965])).

tff(c_980,plain,(
    ! [C_212,A_213,D_214] :
      ( C_212 = A_213
      | k2_yellow_1(A_213) != g1_orders_2(C_212,D_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_977])).

tff(c_983,plain,(
    ! [A_206,A_213] :
      ( u1_struct_0(k2_yellow_1(A_206)) = A_213
      | k2_yellow_1(A_213) != k2_yellow_1(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_980])).

tff(c_997,plain,(
    ! [A_206] : u1_struct_0(k2_yellow_1(A_206)) = A_206 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_983])).

tff(c_999,plain,(
    ! [A_219,B_220] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_219,B_220))) = k9_yellow_6(A_219,B_220)
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1005,plain,(
    ! [A_219,B_220] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_219,B_220))) = u1_struct_0(k9_yellow_6(A_219,B_220))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_219,B_220)))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_36])).

tff(c_1011,plain,(
    ! [A_219,B_220] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_219,B_220))) = u1_struct_0(k9_yellow_6(A_219,B_220))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1005])).

tff(c_1161,plain,(
    ! [A_242,B_243] :
      ( u1_struct_0(k9_yellow_6(A_242,B_243)) = a_2_0_yellow_6(A_242,B_243)
      | ~ m1_subset_1(B_243,u1_struct_0(A_242))
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1011])).

tff(c_1176,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1161])).

tff(c_1184,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1176])).

tff(c_1185,plain,(
    u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1184])).

tff(c_854,plain,(
    r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1189,plain,(
    r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_854])).

tff(c_28,plain,(
    ! [A_8,B_9,C_10] :
      ( '#skF_1'(A_8,B_9,C_10) = A_8
      | ~ r2_hidden(A_8,a_2_0_yellow_6(B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_9))
      | ~ l1_pre_topc(B_9)
      | ~ v2_pre_topc(B_9)
      | v2_struct_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1241,plain,
    ( '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1189,c_28])).

tff(c_1250,plain,
    ( '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1241])).

tff(c_1251,plain,(
    '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1250])).

tff(c_1284,plain,(
    ! [C_253,A_254,B_255] :
      ( r2_hidden(C_253,'#skF_1'(A_254,B_255,C_253))
      | ~ r2_hidden(A_254,a_2_0_yellow_6(B_255,C_253))
      | ~ m1_subset_1(C_253,u1_struct_0(B_255))
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1286,plain,
    ( r2_hidden('#skF_4','#skF_1'('#skF_5','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1189,c_1284])).

tff(c_1292,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1251,c_1286])).

tff(c_1294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_855,c_1292])).

tff(c_1296,plain,(
    ~ v3_pre_topc('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1360,plain,(
    ! [C_272,A_273,D_274,B_275] :
      ( C_272 = A_273
      | g1_orders_2(C_272,D_274) != g1_orders_2(A_273,B_275)
      | ~ m1_subset_1(B_275,k1_zfmisc_1(k2_zfmisc_1(A_273,A_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1368,plain,(
    ! [C_272,A_5,D_274] :
      ( C_272 = A_5
      | k2_yellow_1(A_5) != g1_orders_2(C_272,D_274)
      | ~ m1_subset_1(k1_yellow_1(A_5),k1_zfmisc_1(k2_zfmisc_1(A_5,A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1360])).

tff(c_1371,plain,(
    ! [C_276,A_277,D_278] :
      ( C_276 = A_277
      | k2_yellow_1(A_277) != g1_orders_2(C_276,D_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1368])).

tff(c_1374,plain,(
    ! [A_1,A_277] :
      ( u1_struct_0(A_1) = A_277
      | k2_yellow_1(A_277) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1371])).

tff(c_1391,plain,(
    ! [A_277] :
      ( u1_struct_0(k2_yellow_1(A_277)) = A_277
      | ~ v1_orders_2(k2_yellow_1(A_277))
      | ~ l1_orders_2(k2_yellow_1(A_277)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1374])).

tff(c_1393,plain,(
    ! [A_277] : u1_struct_0(k2_yellow_1(A_277)) = A_277 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_1391])).

tff(c_1409,plain,(
    ! [A_286,B_287] :
      ( k7_lattice3(k2_yellow_1(a_2_0_yellow_6(A_286,B_287))) = k9_yellow_6(A_286,B_287)
      | ~ m1_subset_1(B_287,u1_struct_0(A_286))
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1415,plain,(
    ! [A_286,B_287] :
      ( u1_struct_0(k2_yellow_1(a_2_0_yellow_6(A_286,B_287))) = u1_struct_0(k9_yellow_6(A_286,B_287))
      | ~ l1_orders_2(k2_yellow_1(a_2_0_yellow_6(A_286,B_287)))
      | ~ m1_subset_1(B_287,u1_struct_0(A_286))
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1409,c_36])).

tff(c_1558,plain,(
    ! [A_312,B_313] :
      ( u1_struct_0(k9_yellow_6(A_312,B_313)) = a_2_0_yellow_6(A_312,B_313)
      | ~ m1_subset_1(B_313,u1_struct_0(A_312))
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1393,c_1415])).

tff(c_1573,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1558])).

tff(c_1581,plain,
    ( u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1573])).

tff(c_1582,plain,(
    u1_struct_0(k9_yellow_6('#skF_3','#skF_4')) = a_2_0_yellow_6('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1581])).

tff(c_1295,plain,(
    r2_hidden('#skF_5',u1_struct_0(k9_yellow_6('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1585,plain,(
    r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1582,c_1295])).

tff(c_1603,plain,
    ( '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1585,c_28])).

tff(c_1616,plain,
    ( '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1603])).

tff(c_1617,plain,(
    '#skF_1'('#skF_5','#skF_3','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1616])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( v3_pre_topc('#skF_1'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden(A_8,a_2_0_yellow_6(B_9,C_10))
      | ~ m1_subset_1(C_10,u1_struct_0(B_9))
      | ~ l1_pre_topc(B_9)
      | ~ v2_pre_topc(B_9)
      | v2_struct_0(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1631,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_5',a_2_0_yellow_6('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1617,c_24])).

tff(c_1635,plain,
    ( v3_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1585,c_1631])).

tff(c_1637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1296,c_1635])).

%------------------------------------------------------------------------------
