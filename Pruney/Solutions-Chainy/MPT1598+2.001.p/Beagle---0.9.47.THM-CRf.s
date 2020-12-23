%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:21 EST 2020

% Result     : Theorem 5.57s
% Output     : CNFRefutation 5.57s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 793 expanded)
%              Number of leaves         :   35 ( 319 expanded)
%              Depth                    :   16
%              Number of atoms          :  321 (2363 expanded)
%              Number of equality atoms :   28 ( 200 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k13_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_140,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    ! [A_64] : v5_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_32,plain,(
    ! [A_63] : l1_orders_2(k2_yellow_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1152,plain,(
    ! [A_164,B_165,C_166] :
      ( k13_lattice3(A_164,B_165,C_166) = k10_lattice3(A_164,B_165,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v1_lattice3(A_164)
      | ~ v5_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1158,plain,(
    ! [B_165] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_165,'#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),B_165,'#skF_3')
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1152])).

tff(c_1191,plain,(
    ! [B_171] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_171,'#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),B_171,'#skF_3')
      | ~ m1_subset_1(B_171,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_1158])).

tff(c_1205,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1191])).

tff(c_1156,plain,(
    ! [B_165] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_165,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_165,'#skF_4')
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1152])).

tff(c_1166,plain,(
    ! [B_167] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_167,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_167,'#skF_4')
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_1156])).

tff(c_1181,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1166])).

tff(c_1215,plain,(
    ! [A_172,C_173,B_174] :
      ( k13_lattice3(A_172,C_173,B_174) = k13_lattice3(A_172,B_174,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_172))
      | ~ m1_subset_1(B_174,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v1_lattice3(A_172)
      | ~ v5_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1219,plain,(
    ! [B_174] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_174,'#skF_4') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4',B_174)
      | ~ m1_subset_1(B_174,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1215])).

tff(c_1229,plain,(
    ! [B_175] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_175,'#skF_4') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4',B_175)
      | ~ m1_subset_1(B_175,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_1219])).

tff(c_1239,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1229])).

tff(c_1246,plain,(
    k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1181,c_1239])).

tff(c_122,plain,(
    ! [A_96,B_97,C_98] :
      ( k13_lattice3(A_96,B_97,C_98) = k10_lattice3(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v1_lattice3(A_96)
      | ~ v5_orders_2(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_126,plain,(
    ! [B_97] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_137,plain,(
    ! [B_99] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4')
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_126])).

tff(c_152,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_128,plain,(
    ! [B_97] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_3')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_161,plain,(
    ! [B_100] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),B_100,'#skF_3')
      | ~ m1_subset_1(B_100,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_128])).

tff(c_175,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_161])).

tff(c_245,plain,(
    ! [A_109,C_110,B_111] :
      ( k13_lattice3(A_109,C_110,B_111) = k13_lattice3(A_109,B_111,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(A_109))
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v1_lattice3(A_109)
      | ~ v5_orders_2(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_251,plain,(
    ! [B_111] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_111,'#skF_3') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_111)
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_261,plain,(
    ! [B_112] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_112,'#skF_3') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3',B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_251])).

tff(c_268,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_261])).

tff(c_276,plain,(
    k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_175,c_268])).

tff(c_62,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(k2_xboole_0(A_82,C_83),B_84)
      | ~ r1_tarski(C_83,B_84)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_46])).

tff(c_67,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_280,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_67])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k10_lattice3(A_11,B_12,C_13),u1_struct_0(A_11))
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_285,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_12])).

tff(c_289,plain,(
    m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_48,c_285])).

tff(c_279,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_152])).

tff(c_28,plain,(
    ! [A_17,B_41,C_53] :
      ( r1_orders_2(A_17,B_41,k13_lattice3(A_17,B_41,C_53))
      | ~ m1_subset_1(k13_lattice3(A_17,B_41,C_53),u1_struct_0(A_17))
      | ~ m1_subset_1(C_53,u1_struct_0(A_17))
      | ~ m1_subset_1(B_41,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | ~ v1_lattice3(A_17)
      | ~ v5_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_359,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_28])).

tff(c_363,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_50,c_48,c_289,c_279,c_359])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_36,plain,(
    ! [A_64] : v3_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_186,plain,(
    ! [A_104,B_105,C_106] :
      ( r3_orders_2(A_104,B_105,C_106)
      | ~ r1_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_190,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_186])).

tff(c_196,plain,(
    ! [B_105] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_190])).

tff(c_200,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_200,c_8])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52,c_203])).

tff(c_209,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r3_orders_2(A_4,B_5,C_6)
      | ~ r1_orders_2(A_4,B_5,C_6)
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_307,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_289,c_4])).

tff(c_332,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_307])).

tff(c_1021,plain,(
    ! [B_148] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_148,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_332])).

tff(c_44,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_69,u1_struct_0(k2_yellow_1(A_65)))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1025,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_148,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1021,c_44])).

tff(c_1032,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_148,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_148,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_1025])).

tff(c_1065,plain,(
    ! [B_152] :
      ( r1_tarski(B_152,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_152,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_152,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1032])).

tff(c_1079,plain,
    ( r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_363,c_1065])).

tff(c_1092,plain,(
    r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1079])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_1092])).

tff(c_1095,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1249,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1095])).

tff(c_1254,plain,
    ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_12])).

tff(c_1258,plain,(
    m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_48,c_1254])).

tff(c_1360,plain,(
    ! [A_181,B_182,C_183] :
      ( r1_orders_2(A_181,B_182,k13_lattice3(A_181,B_182,C_183))
      | ~ m1_subset_1(k13_lattice3(A_181,B_182,C_183),u1_struct_0(A_181))
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v1_lattice3(A_181)
      | ~ v5_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1366,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_4',k13_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_1360])).

tff(c_1374,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),'#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_32,c_48,c_50,c_1258,c_1205,c_1366])).

tff(c_1260,plain,(
    ! [A_176,B_177,C_178] :
      ( r3_orders_2(A_176,B_177,C_178)
      | ~ r1_orders_2(A_176,B_177,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0(A_176))
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1266,plain,(
    ! [B_177] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_177,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_177,'#skF_3')
      | ~ m1_subset_1(B_177,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1260])).

tff(c_1273,plain,(
    ! [B_177] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_177,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_177,'#skF_3')
      | ~ m1_subset_1(B_177,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1266])).

tff(c_1377,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_1381,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1377,c_8])).

tff(c_1385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52,c_1381])).

tff(c_1387,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_2754,plain,(
    ! [A_238,B_239,B_240,C_241] :
      ( r3_orders_2(A_238,B_239,k10_lattice3(A_238,B_240,C_241))
      | ~ r1_orders_2(A_238,B_239,k10_lattice3(A_238,B_240,C_241))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ v3_orders_2(A_238)
      | v2_struct_0(A_238)
      | ~ m1_subset_1(C_241,u1_struct_0(A_238))
      | ~ m1_subset_1(B_240,u1_struct_0(A_238))
      | ~ l1_orders_2(A_238) ) ),
    inference(resolution,[status(thm)],[c_12,c_1260])).

tff(c_2768,plain,(
    ! [B_239] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_239,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_239,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_239,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1246,c_2754])).

tff(c_2780,plain,(
    ! [B_239] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_239,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_239,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_239,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_50,c_48,c_36,c_1246,c_2768])).

tff(c_3191,plain,(
    ! [B_253] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_253,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1387,c_2780])).

tff(c_3195,plain,(
    ! [B_253] :
      ( r1_tarski(B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_253,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_3191,c_44])).

tff(c_3202,plain,(
    ! [B_253] :
      ( r1_tarski(B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_253,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_253,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_3195])).

tff(c_3204,plain,(
    ! [B_254] :
      ( r1_tarski(B_254,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_254,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(B_254,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3202])).

tff(c_3219,plain,
    ( r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1374,c_3204])).

tff(c_3234,plain,(
    r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3219])).

tff(c_3236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1249,c_3234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.57/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.05  
% 5.57/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.05  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.57/2.05  
% 5.57/2.05  %Foreground sorts:
% 5.57/2.05  
% 5.57/2.05  
% 5.57/2.05  %Background operators:
% 5.57/2.05  
% 5.57/2.05  
% 5.57/2.05  %Foreground operators:
% 5.57/2.05  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 5.57/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.57/2.05  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.57/2.05  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.57/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.57/2.05  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 5.57/2.05  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.57/2.05  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 5.57/2.05  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.57/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.57/2.05  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.57/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.57/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.57/2.05  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.57/2.05  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.57/2.05  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.57/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.57/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.57/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.57/2.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.57/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.57/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.57/2.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.57/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.57/2.05  
% 5.57/2.07  tff(f_154, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_1)).
% 5.57/2.07  tff(f_127, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 5.57/2.07  tff(f_119, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 5.57/2.07  tff(f_85, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 5.57/2.07  tff(f_65, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k13_lattice3(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k13_lattice3)).
% 5.57/2.07  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.57/2.07  tff(f_73, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 5.57/2.07  tff(f_115, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_0)).
% 5.57/2.07  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 5.57/2.07  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 5.57/2.07  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 5.57/2.07  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.57/2.07  tff(c_40, plain, (![A_64]: (v5_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.57/2.07  tff(c_52, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.57/2.07  tff(c_32, plain, (![A_63]: (l1_orders_2(k2_yellow_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.57/2.07  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.57/2.07  tff(c_1152, plain, (![A_164, B_165, C_166]: (k13_lattice3(A_164, B_165, C_166)=k10_lattice3(A_164, B_165, C_166) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v1_lattice3(A_164) | ~v5_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.57/2.07  tff(c_1158, plain, (![B_165]: (k13_lattice3(k2_yellow_1('#skF_2'), B_165, '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), B_165, '#skF_3') | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_1152])).
% 5.57/2.07  tff(c_1191, plain, (![B_171]: (k13_lattice3(k2_yellow_1('#skF_2'), B_171, '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), B_171, '#skF_3') | ~m1_subset_1(B_171, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_1158])).
% 5.57/2.07  tff(c_1205, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_1191])).
% 5.57/2.07  tff(c_1156, plain, (![B_165]: (k13_lattice3(k2_yellow_1('#skF_2'), B_165, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_165, '#skF_4') | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_1152])).
% 5.57/2.07  tff(c_1166, plain, (![B_167]: (k13_lattice3(k2_yellow_1('#skF_2'), B_167, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_167, '#skF_4') | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_1156])).
% 5.57/2.07  tff(c_1181, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1166])).
% 5.57/2.07  tff(c_1215, plain, (![A_172, C_173, B_174]: (k13_lattice3(A_172, C_173, B_174)=k13_lattice3(A_172, B_174, C_173) | ~m1_subset_1(C_173, u1_struct_0(A_172)) | ~m1_subset_1(B_174, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v1_lattice3(A_172) | ~v5_orders_2(A_172))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.57/2.07  tff(c_1219, plain, (![B_174]: (k13_lattice3(k2_yellow_1('#skF_2'), B_174, '#skF_4')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', B_174) | ~m1_subset_1(B_174, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_1215])).
% 5.57/2.07  tff(c_1229, plain, (![B_175]: (k13_lattice3(k2_yellow_1('#skF_2'), B_175, '#skF_4')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', B_175) | ~m1_subset_1(B_175, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_1219])).
% 5.57/2.07  tff(c_1239, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1229])).
% 5.57/2.07  tff(c_1246, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1181, c_1239])).
% 5.57/2.07  tff(c_122, plain, (![A_96, B_97, C_98]: (k13_lattice3(A_96, B_97, C_98)=k10_lattice3(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v1_lattice3(A_96) | ~v5_orders_2(A_96))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.57/2.07  tff(c_126, plain, (![B_97]: (k13_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_122])).
% 5.57/2.07  tff(c_137, plain, (![B_99]: (k13_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4') | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_126])).
% 5.57/2.07  tff(c_152, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_137])).
% 5.57/2.07  tff(c_128, plain, (![B_97]: (k13_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_3') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_122])).
% 5.57/2.07  tff(c_161, plain, (![B_100]: (k13_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), B_100, '#skF_3') | ~m1_subset_1(B_100, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_128])).
% 5.57/2.07  tff(c_175, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_161])).
% 5.57/2.07  tff(c_245, plain, (![A_109, C_110, B_111]: (k13_lattice3(A_109, C_110, B_111)=k13_lattice3(A_109, B_111, C_110) | ~m1_subset_1(C_110, u1_struct_0(A_109)) | ~m1_subset_1(B_111, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v1_lattice3(A_109) | ~v5_orders_2(A_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.57/2.07  tff(c_251, plain, (![B_111]: (k13_lattice3(k2_yellow_1('#skF_2'), B_111, '#skF_3')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_111) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_245])).
% 5.57/2.07  tff(c_261, plain, (![B_112]: (k13_lattice3(k2_yellow_1('#skF_2'), B_112, '#skF_3')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', B_112) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_251])).
% 5.57/2.07  tff(c_268, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_261])).
% 5.57/2.07  tff(c_276, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_175, c_268])).
% 5.57/2.07  tff(c_62, plain, (![A_82, C_83, B_84]: (r1_tarski(k2_xboole_0(A_82, C_83), B_84) | ~r1_tarski(C_83, B_84) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.57/2.07  tff(c_46, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.57/2.07  tff(c_66, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_46])).
% 5.57/2.07  tff(c_67, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.57/2.07  tff(c_280, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_67])).
% 5.57/2.07  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_subset_1(k10_lattice3(A_11, B_12, C_13), u1_struct_0(A_11)) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.57/2.07  tff(c_285, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_12])).
% 5.57/2.07  tff(c_289, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_48, c_285])).
% 5.57/2.07  tff(c_279, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_152])).
% 5.57/2.07  tff(c_28, plain, (![A_17, B_41, C_53]: (r1_orders_2(A_17, B_41, k13_lattice3(A_17, B_41, C_53)) | ~m1_subset_1(k13_lattice3(A_17, B_41, C_53), u1_struct_0(A_17)) | ~m1_subset_1(C_53, u1_struct_0(A_17)) | ~m1_subset_1(B_41, u1_struct_0(A_17)) | ~l1_orders_2(A_17) | ~v1_lattice3(A_17) | ~v5_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.57/2.07  tff(c_359, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_279, c_28])).
% 5.57/2.07  tff(c_363, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_50, c_48, c_289, c_279, c_359])).
% 5.57/2.07  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.57/2.07  tff(c_36, plain, (![A_64]: (v3_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.57/2.07  tff(c_186, plain, (![A_104, B_105, C_106]: (r3_orders_2(A_104, B_105, C_106) | ~r1_orders_2(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.57/2.07  tff(c_190, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_186])).
% 5.57/2.07  tff(c_196, plain, (![B_105]: (r3_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_190])).
% 5.57/2.07  tff(c_200, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_196])).
% 5.57/2.07  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.57/2.07  tff(c_203, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_200, c_8])).
% 5.57/2.07  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_52, c_203])).
% 5.57/2.07  tff(c_209, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_196])).
% 5.57/2.07  tff(c_4, plain, (![A_4, B_5, C_6]: (r3_orders_2(A_4, B_5, C_6) | ~r1_orders_2(A_4, B_5, C_6) | ~m1_subset_1(C_6, u1_struct_0(A_4)) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.57/2.07  tff(c_307, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_289, c_4])).
% 5.57/2.07  tff(c_332, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_307])).
% 5.57/2.07  tff(c_1021, plain, (![B_148]: (r3_orders_2(k2_yellow_1('#skF_2'), B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_148, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_209, c_332])).
% 5.57/2.07  tff(c_44, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_69, u1_struct_0(k2_yellow_1(A_65))) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.57/2.07  tff(c_1025, plain, (![B_148]: (r1_tarski(B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_148, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(resolution, [status(thm)], [c_1021, c_44])).
% 5.57/2.07  tff(c_1032, plain, (![B_148]: (r1_tarski(B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_148, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_148, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_289, c_1025])).
% 5.57/2.07  tff(c_1065, plain, (![B_152]: (r1_tarski(B_152, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_152, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_152, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_1032])).
% 5.57/2.07  tff(c_1079, plain, (r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_363, c_1065])).
% 5.57/2.07  tff(c_1092, plain, (r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1079])).
% 5.57/2.07  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_1092])).
% 5.57/2.07  tff(c_1095, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 5.57/2.07  tff(c_1249, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1095])).
% 5.57/2.07  tff(c_1254, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1246, c_12])).
% 5.57/2.07  tff(c_1258, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_48, c_1254])).
% 5.57/2.07  tff(c_1360, plain, (![A_181, B_182, C_183]: (r1_orders_2(A_181, B_182, k13_lattice3(A_181, B_182, C_183)) | ~m1_subset_1(k13_lattice3(A_181, B_182, C_183), u1_struct_0(A_181)) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v1_lattice3(A_181) | ~v5_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.57/2.07  tff(c_1366, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_4', k13_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1205, c_1360])).
% 5.57/2.07  tff(c_1374, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52, c_32, c_48, c_50, c_1258, c_1205, c_1366])).
% 5.57/2.07  tff(c_1260, plain, (![A_176, B_177, C_178]: (r3_orders_2(A_176, B_177, C_178) | ~r1_orders_2(A_176, B_177, C_178) | ~m1_subset_1(C_178, u1_struct_0(A_176)) | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~l1_orders_2(A_176) | ~v3_orders_2(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.57/2.07  tff(c_1266, plain, (![B_177]: (r3_orders_2(k2_yellow_1('#skF_2'), B_177, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_177, '#skF_3') | ~m1_subset_1(B_177, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_1260])).
% 5.57/2.07  tff(c_1273, plain, (![B_177]: (r3_orders_2(k2_yellow_1('#skF_2'), B_177, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_177, '#skF_3') | ~m1_subset_1(B_177, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_1266])).
% 5.57/2.07  tff(c_1377, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1273])).
% 5.57/2.07  tff(c_1381, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_1377, c_8])).
% 5.57/2.07  tff(c_1385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_52, c_1381])).
% 5.57/2.07  tff(c_1387, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1273])).
% 5.57/2.07  tff(c_2754, plain, (![A_238, B_239, B_240, C_241]: (r3_orders_2(A_238, B_239, k10_lattice3(A_238, B_240, C_241)) | ~r1_orders_2(A_238, B_239, k10_lattice3(A_238, B_240, C_241)) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~v3_orders_2(A_238) | v2_struct_0(A_238) | ~m1_subset_1(C_241, u1_struct_0(A_238)) | ~m1_subset_1(B_240, u1_struct_0(A_238)) | ~l1_orders_2(A_238))), inference(resolution, [status(thm)], [c_12, c_1260])).
% 5.57/2.07  tff(c_2768, plain, (![B_239]: (r3_orders_2(k2_yellow_1('#skF_2'), B_239, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_239, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_239, u1_struct_0(k2_yellow_1('#skF_2'))) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1246, c_2754])).
% 5.57/2.07  tff(c_2780, plain, (![B_239]: (r3_orders_2(k2_yellow_1('#skF_2'), B_239, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_239, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_239, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_50, c_48, c_36, c_1246, c_2768])).
% 5.57/2.07  tff(c_3191, plain, (![B_253]: (r3_orders_2(k2_yellow_1('#skF_2'), B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_253, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1387, c_2780])).
% 5.57/2.07  tff(c_3195, plain, (![B_253]: (r1_tarski(B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_253, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(resolution, [status(thm)], [c_3191, c_44])).
% 5.57/2.07  tff(c_3202, plain, (![B_253]: (r1_tarski(B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_253, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_253, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_3195])).
% 5.57/2.07  tff(c_3204, plain, (![B_254]: (r1_tarski(B_254, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_254, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1(B_254, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_3202])).
% 5.57/2.07  tff(c_3219, plain, (r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_1374, c_3204])).
% 5.57/2.07  tff(c_3234, plain, (r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3219])).
% 5.57/2.07  tff(c_3236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1249, c_3234])).
% 5.57/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.57/2.07  
% 5.57/2.07  Inference rules
% 5.57/2.07  ----------------------
% 5.57/2.07  #Ref     : 0
% 5.57/2.07  #Sup     : 691
% 5.57/2.07  #Fact    : 0
% 5.57/2.07  #Define  : 0
% 5.57/2.07  #Split   : 50
% 5.57/2.07  #Chain   : 0
% 5.57/2.07  #Close   : 0
% 5.57/2.07  
% 5.57/2.07  Ordering : KBO
% 5.57/2.07  
% 5.57/2.07  Simplification rules
% 5.57/2.07  ----------------------
% 5.57/2.07  #Subsume      : 17
% 5.57/2.07  #Demod        : 1633
% 5.57/2.07  #Tautology    : 188
% 5.57/2.07  #SimpNegUnit  : 64
% 5.57/2.07  #BackRed      : 22
% 5.57/2.07  
% 5.57/2.07  #Partial instantiations: 0
% 5.57/2.07  #Strategies tried      : 1
% 5.57/2.07  
% 5.57/2.07  Timing (in seconds)
% 5.57/2.07  ----------------------
% 5.57/2.08  Preprocessing        : 0.35
% 5.57/2.08  Parsing              : 0.18
% 5.57/2.08  CNF conversion       : 0.03
% 5.57/2.08  Main loop            : 0.95
% 5.57/2.08  Inferencing          : 0.30
% 5.57/2.08  Reduction            : 0.37
% 5.57/2.08  Demodulation         : 0.26
% 5.57/2.08  BG Simplification    : 0.04
% 5.57/2.08  Subsumption          : 0.18
% 5.57/2.08  Abstraction          : 0.06
% 5.57/2.08  MUC search           : 0.00
% 5.57/2.08  Cooper               : 0.00
% 5.57/2.08  Total                : 1.34
% 5.57/2.08  Index Insertion      : 0.00
% 5.57/2.08  Index Deletion       : 0.00
% 5.57/2.08  Index Matching       : 0.00
% 5.57/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
