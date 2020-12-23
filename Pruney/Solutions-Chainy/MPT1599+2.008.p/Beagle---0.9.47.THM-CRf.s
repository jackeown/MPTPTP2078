%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 185 expanded)
%              Number of leaves         :   37 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 482 expanded)
%              Number of equality atoms :    4 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_112,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(c_30,plain,(
    ! [A_59] : l1_orders_2(k2_yellow_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    ! [A_61] : u1_struct_0(k2_yellow_1(A_61)) = A_61 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_57,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_58,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_50])).

tff(c_216,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k11_lattice3(A_140,B_141,C_142),u1_struct_0(A_140))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_219,plain,(
    ! [A_61,B_141,C_142] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_61),B_141,C_142),A_61)
      | ~ m1_subset_1(C_142,u1_struct_0(k2_yellow_1(A_61)))
      | ~ m1_subset_1(B_141,u1_struct_0(k2_yellow_1(A_61)))
      | ~ l1_orders_2(k2_yellow_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_216])).

tff(c_221,plain,(
    ! [A_61,B_141,C_142] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_61),B_141,C_142),A_61)
      | ~ m1_subset_1(C_142,A_61)
      | ~ m1_subset_1(B_141,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_40,c_219])).

tff(c_38,plain,(
    ! [A_60] : v5_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k11_lattice3(A_10,B_11,C_12),u1_struct_0(A_10))
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_282,plain,(
    ! [A_173,B_174,C_175] :
      ( r1_orders_2(A_173,k11_lattice3(A_173,B_174,C_175),C_175)
      | ~ m1_subset_1(k11_lattice3(A_173,B_174,C_175),u1_struct_0(A_173))
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173)
      | ~ v2_lattice3(A_173)
      | ~ v5_orders_2(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_291,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_orders_2(A_179,k11_lattice3(A_179,B_180,C_181),C_181)
      | ~ v2_lattice3(A_179)
      | ~ v5_orders_2(A_179)
      | v2_struct_0(A_179)
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179) ) ),
    inference(resolution,[status(thm)],[c_12,c_282])).

tff(c_34,plain,(
    ! [A_60] : v3_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_230,plain,(
    ! [A_152,B_153,C_154] :
      ( r3_orders_2(A_152,B_153,C_154)
      | ~ r1_orders_2(A_152,B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_orders_2(A_152)
      | ~ v3_orders_2(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_237,plain,(
    ! [A_61,B_153,C_154] :
      ( r3_orders_2(k2_yellow_1(A_61),B_153,C_154)
      | ~ r1_orders_2(k2_yellow_1(A_61),B_153,C_154)
      | ~ m1_subset_1(C_154,A_61)
      | ~ m1_subset_1(B_153,u1_struct_0(k2_yellow_1(A_61)))
      | ~ l1_orders_2(k2_yellow_1(A_61))
      | ~ v3_orders_2(k2_yellow_1(A_61))
      | v2_struct_0(k2_yellow_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_230])).

tff(c_242,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_orders_2(k2_yellow_1(A_155),B_156,C_157)
      | ~ r1_orders_2(k2_yellow_1(A_155),B_156,C_157)
      | ~ m1_subset_1(C_157,A_155)
      | ~ m1_subset_1(B_156,A_155)
      | v2_struct_0(k2_yellow_1(A_155)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_40,c_237])).

tff(c_46,plain,(
    ! [B_66,C_68,A_62] :
      ( r1_tarski(B_66,C_68)
      | ~ r3_orders_2(k2_yellow_1(A_62),B_66,C_68)
      | ~ m1_subset_1(C_68,u1_struct_0(k2_yellow_1(A_62)))
      | ~ m1_subset_1(B_66,u1_struct_0(k2_yellow_1(A_62)))
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_59,plain,(
    ! [B_66,C_68,A_62] :
      ( r1_tarski(B_66,C_68)
      | ~ r3_orders_2(k2_yellow_1(A_62),B_66,C_68)
      | ~ m1_subset_1(C_68,A_62)
      | ~ m1_subset_1(B_66,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_46])).

tff(c_251,plain,(
    ! [B_156,C_157,A_155] :
      ( r1_tarski(B_156,C_157)
      | v1_xboole_0(A_155)
      | ~ r1_orders_2(k2_yellow_1(A_155),B_156,C_157)
      | ~ m1_subset_1(C_157,A_155)
      | ~ m1_subset_1(B_156,A_155)
      | v2_struct_0(k2_yellow_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_242,c_59])).

tff(c_295,plain,(
    ! [A_155,B_180,C_181] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_155),B_180,C_181),C_181)
      | v1_xboole_0(A_155)
      | ~ m1_subset_1(C_181,A_155)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_155),B_180,C_181),A_155)
      | ~ v2_lattice3(k2_yellow_1(A_155))
      | ~ v5_orders_2(k2_yellow_1(A_155))
      | v2_struct_0(k2_yellow_1(A_155))
      | ~ m1_subset_1(C_181,u1_struct_0(k2_yellow_1(A_155)))
      | ~ m1_subset_1(B_180,u1_struct_0(k2_yellow_1(A_155)))
      | ~ l1_orders_2(k2_yellow_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_291,c_251])).

tff(c_304,plain,(
    ! [A_185,B_186,C_187] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_185),B_186,C_187),C_187)
      | v1_xboole_0(A_185)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_185),B_186,C_187),A_185)
      | ~ v2_lattice3(k2_yellow_1(A_185))
      | v2_struct_0(k2_yellow_1(A_185))
      | ~ m1_subset_1(C_187,A_185)
      | ~ m1_subset_1(B_186,A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_40,c_38,c_295])).

tff(c_317,plain,(
    ! [A_192,B_193,C_194] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_192),B_193,C_194),C_194)
      | v1_xboole_0(A_192)
      | ~ v2_lattice3(k2_yellow_1(A_192))
      | v2_struct_0(k2_yellow_1(A_192))
      | ~ m1_subset_1(C_194,A_192)
      | ~ m1_subset_1(B_193,A_192) ) ),
    inference(resolution,[status(thm)],[c_221,c_304])).

tff(c_107,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k11_lattice3(A_92,B_93,C_94),u1_struct_0(A_92))
      | ~ m1_subset_1(C_94,u1_struct_0(A_92))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_orders_2(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_110,plain,(
    ! [A_61,B_93,C_94] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_61),B_93,C_94),A_61)
      | ~ m1_subset_1(C_94,u1_struct_0(k2_yellow_1(A_61)))
      | ~ m1_subset_1(B_93,u1_struct_0(k2_yellow_1(A_61)))
      | ~ l1_orders_2(k2_yellow_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_107])).

tff(c_112,plain,(
    ! [A_61,B_93,C_94] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_61),B_93,C_94),A_61)
      | ~ m1_subset_1(C_94,A_61)
      | ~ m1_subset_1(B_93,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_40,c_110])).

tff(c_169,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_orders_2(A_122,k11_lattice3(A_122,B_123,C_124),B_123)
      | ~ m1_subset_1(k11_lattice3(A_122,B_123,C_124),u1_struct_0(A_122))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v2_lattice3(A_122)
      | ~ v5_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,(
    ! [A_125,B_126,C_127] :
      ( r1_orders_2(A_125,k11_lattice3(A_125,B_126,C_127),B_126)
      | ~ v2_lattice3(A_125)
      | ~ v5_orders_2(A_125)
      | v2_struct_0(A_125)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125) ) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_114,plain,(
    ! [A_98,B_99,C_100] :
      ( r3_orders_2(A_98,B_99,C_100)
      | ~ r1_orders_2(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_121,plain,(
    ! [A_61,B_99,C_100] :
      ( r3_orders_2(k2_yellow_1(A_61),B_99,C_100)
      | ~ r1_orders_2(k2_yellow_1(A_61),B_99,C_100)
      | ~ m1_subset_1(C_100,A_61)
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1(A_61)))
      | ~ l1_orders_2(k2_yellow_1(A_61))
      | ~ v3_orders_2(k2_yellow_1(A_61))
      | v2_struct_0(k2_yellow_1(A_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_114])).

tff(c_126,plain,(
    ! [A_101,B_102,C_103] :
      ( r3_orders_2(k2_yellow_1(A_101),B_102,C_103)
      | ~ r1_orders_2(k2_yellow_1(A_101),B_102,C_103)
      | ~ m1_subset_1(C_103,A_101)
      | ~ m1_subset_1(B_102,A_101)
      | v2_struct_0(k2_yellow_1(A_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_40,c_121])).

tff(c_130,plain,(
    ! [B_102,C_103,A_101] :
      ( r1_tarski(B_102,C_103)
      | v1_xboole_0(A_101)
      | ~ r1_orders_2(k2_yellow_1(A_101),B_102,C_103)
      | ~ m1_subset_1(C_103,A_101)
      | ~ m1_subset_1(B_102,A_101)
      | v2_struct_0(k2_yellow_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_126,c_59])).

tff(c_181,plain,(
    ! [A_101,B_126,C_127] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_101),B_126,C_127),B_126)
      | v1_xboole_0(A_101)
      | ~ m1_subset_1(B_126,A_101)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_101),B_126,C_127),A_101)
      | ~ v2_lattice3(k2_yellow_1(A_101))
      | ~ v5_orders_2(k2_yellow_1(A_101))
      | v2_struct_0(k2_yellow_1(A_101))
      | ~ m1_subset_1(C_127,u1_struct_0(k2_yellow_1(A_101)))
      | ~ m1_subset_1(B_126,u1_struct_0(k2_yellow_1(A_101)))
      | ~ l1_orders_2(k2_yellow_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_177,c_130])).

tff(c_190,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_131),B_132,C_133),B_132)
      | v1_xboole_0(A_131)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1(A_131),B_132,C_133),A_131)
      | ~ v2_lattice3(k2_yellow_1(A_131))
      | v2_struct_0(k2_yellow_1(A_131))
      | ~ m1_subset_1(C_133,A_131)
      | ~ m1_subset_1(B_132,A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_40,c_38,c_181])).

tff(c_194,plain,(
    ! [A_134,B_135,C_136] :
      ( r1_tarski(k11_lattice3(k2_yellow_1(A_134),B_135,C_136),B_135)
      | v1_xboole_0(A_134)
      | ~ v2_lattice3(k2_yellow_1(A_134))
      | v2_struct_0(k2_yellow_1(A_134))
      | ~ m1_subset_1(C_136,A_134)
      | ~ m1_subset_1(B_135,A_134) ) ),
    inference(resolution,[status(thm)],[c_112,c_190])).

tff(c_95,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(A_83,k3_xboole_0(B_84,C_85))
      | ~ r1_tarski(A_83,C_85)
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_99,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_48])).

tff(c_101,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_197,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_194,c_101])).

tff(c_200,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_54,c_197])).

tff(c_201,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_200])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v2_struct_0(A_9)
      | ~ v2_lattice3(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_204,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_201,c_10])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_54,c_204])).

tff(c_209,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_320,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_317,c_209])).

tff(c_323,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_54,c_320])).

tff(c_324,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_323])).

tff(c_327,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_324,c_10])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_54,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:02:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.47/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.35  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.47/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.47/1.35  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.47/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.47/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.47/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.35  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.47/1.35  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.47/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.35  
% 2.47/1.37  tff(f_100, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.47/1.37  tff(f_139, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 2.47/1.37  tff(f_112, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.47/1.37  tff(f_63, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 2.47/1.37  tff(f_108, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.47/1.37  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 2.47/1.37  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.47/1.37  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.47/1.37  tff(f_55, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 2.47/1.37  tff(c_30, plain, (![A_59]: (l1_orders_2(k2_yellow_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.47/1.37  tff(c_54, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.47/1.37  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.47/1.37  tff(c_40, plain, (![A_61]: (u1_struct_0(k2_yellow_1(A_61))=A_61)), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.47/1.37  tff(c_52, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.47/1.37  tff(c_57, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 2.47/1.37  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.47/1.37  tff(c_58, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_50])).
% 2.47/1.37  tff(c_216, plain, (![A_140, B_141, C_142]: (m1_subset_1(k11_lattice3(A_140, B_141, C_142), u1_struct_0(A_140)) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.37  tff(c_219, plain, (![A_61, B_141, C_142]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_61), B_141, C_142), A_61) | ~m1_subset_1(C_142, u1_struct_0(k2_yellow_1(A_61))) | ~m1_subset_1(B_141, u1_struct_0(k2_yellow_1(A_61))) | ~l1_orders_2(k2_yellow_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_216])).
% 2.47/1.37  tff(c_221, plain, (![A_61, B_141, C_142]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_61), B_141, C_142), A_61) | ~m1_subset_1(C_142, A_61) | ~m1_subset_1(B_141, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_40, c_219])).
% 2.47/1.37  tff(c_38, plain, (![A_60]: (v5_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.47/1.37  tff(c_12, plain, (![A_10, B_11, C_12]: (m1_subset_1(k11_lattice3(A_10, B_11, C_12), u1_struct_0(A_10)) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.37  tff(c_282, plain, (![A_173, B_174, C_175]: (r1_orders_2(A_173, k11_lattice3(A_173, B_174, C_175), C_175) | ~m1_subset_1(k11_lattice3(A_173, B_174, C_175), u1_struct_0(A_173)) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v2_lattice3(A_173) | ~v5_orders_2(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.47/1.37  tff(c_291, plain, (![A_179, B_180, C_181]: (r1_orders_2(A_179, k11_lattice3(A_179, B_180, C_181), C_181) | ~v2_lattice3(A_179) | ~v5_orders_2(A_179) | v2_struct_0(A_179) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179))), inference(resolution, [status(thm)], [c_12, c_282])).
% 2.47/1.37  tff(c_34, plain, (![A_60]: (v3_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.47/1.37  tff(c_230, plain, (![A_152, B_153, C_154]: (r3_orders_2(A_152, B_153, C_154) | ~r1_orders_2(A_152, B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_orders_2(A_152) | ~v3_orders_2(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.37  tff(c_237, plain, (![A_61, B_153, C_154]: (r3_orders_2(k2_yellow_1(A_61), B_153, C_154) | ~r1_orders_2(k2_yellow_1(A_61), B_153, C_154) | ~m1_subset_1(C_154, A_61) | ~m1_subset_1(B_153, u1_struct_0(k2_yellow_1(A_61))) | ~l1_orders_2(k2_yellow_1(A_61)) | ~v3_orders_2(k2_yellow_1(A_61)) | v2_struct_0(k2_yellow_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_230])).
% 2.47/1.37  tff(c_242, plain, (![A_155, B_156, C_157]: (r3_orders_2(k2_yellow_1(A_155), B_156, C_157) | ~r1_orders_2(k2_yellow_1(A_155), B_156, C_157) | ~m1_subset_1(C_157, A_155) | ~m1_subset_1(B_156, A_155) | v2_struct_0(k2_yellow_1(A_155)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_40, c_237])).
% 2.47/1.37  tff(c_46, plain, (![B_66, C_68, A_62]: (r1_tarski(B_66, C_68) | ~r3_orders_2(k2_yellow_1(A_62), B_66, C_68) | ~m1_subset_1(C_68, u1_struct_0(k2_yellow_1(A_62))) | ~m1_subset_1(B_66, u1_struct_0(k2_yellow_1(A_62))) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.47/1.37  tff(c_59, plain, (![B_66, C_68, A_62]: (r1_tarski(B_66, C_68) | ~r3_orders_2(k2_yellow_1(A_62), B_66, C_68) | ~m1_subset_1(C_68, A_62) | ~m1_subset_1(B_66, A_62) | v1_xboole_0(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_46])).
% 2.47/1.37  tff(c_251, plain, (![B_156, C_157, A_155]: (r1_tarski(B_156, C_157) | v1_xboole_0(A_155) | ~r1_orders_2(k2_yellow_1(A_155), B_156, C_157) | ~m1_subset_1(C_157, A_155) | ~m1_subset_1(B_156, A_155) | v2_struct_0(k2_yellow_1(A_155)))), inference(resolution, [status(thm)], [c_242, c_59])).
% 2.47/1.37  tff(c_295, plain, (![A_155, B_180, C_181]: (r1_tarski(k11_lattice3(k2_yellow_1(A_155), B_180, C_181), C_181) | v1_xboole_0(A_155) | ~m1_subset_1(C_181, A_155) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_155), B_180, C_181), A_155) | ~v2_lattice3(k2_yellow_1(A_155)) | ~v5_orders_2(k2_yellow_1(A_155)) | v2_struct_0(k2_yellow_1(A_155)) | ~m1_subset_1(C_181, u1_struct_0(k2_yellow_1(A_155))) | ~m1_subset_1(B_180, u1_struct_0(k2_yellow_1(A_155))) | ~l1_orders_2(k2_yellow_1(A_155)))), inference(resolution, [status(thm)], [c_291, c_251])).
% 2.47/1.37  tff(c_304, plain, (![A_185, B_186, C_187]: (r1_tarski(k11_lattice3(k2_yellow_1(A_185), B_186, C_187), C_187) | v1_xboole_0(A_185) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_185), B_186, C_187), A_185) | ~v2_lattice3(k2_yellow_1(A_185)) | v2_struct_0(k2_yellow_1(A_185)) | ~m1_subset_1(C_187, A_185) | ~m1_subset_1(B_186, A_185))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_40, c_38, c_295])).
% 2.47/1.37  tff(c_317, plain, (![A_192, B_193, C_194]: (r1_tarski(k11_lattice3(k2_yellow_1(A_192), B_193, C_194), C_194) | v1_xboole_0(A_192) | ~v2_lattice3(k2_yellow_1(A_192)) | v2_struct_0(k2_yellow_1(A_192)) | ~m1_subset_1(C_194, A_192) | ~m1_subset_1(B_193, A_192))), inference(resolution, [status(thm)], [c_221, c_304])).
% 2.47/1.37  tff(c_107, plain, (![A_92, B_93, C_94]: (m1_subset_1(k11_lattice3(A_92, B_93, C_94), u1_struct_0(A_92)) | ~m1_subset_1(C_94, u1_struct_0(A_92)) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_orders_2(A_92))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.37  tff(c_110, plain, (![A_61, B_93, C_94]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_61), B_93, C_94), A_61) | ~m1_subset_1(C_94, u1_struct_0(k2_yellow_1(A_61))) | ~m1_subset_1(B_93, u1_struct_0(k2_yellow_1(A_61))) | ~l1_orders_2(k2_yellow_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_107])).
% 2.47/1.37  tff(c_112, plain, (![A_61, B_93, C_94]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_61), B_93, C_94), A_61) | ~m1_subset_1(C_94, A_61) | ~m1_subset_1(B_93, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_40, c_110])).
% 2.47/1.37  tff(c_169, plain, (![A_122, B_123, C_124]: (r1_orders_2(A_122, k11_lattice3(A_122, B_123, C_124), B_123) | ~m1_subset_1(k11_lattice3(A_122, B_123, C_124), u1_struct_0(A_122)) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v2_lattice3(A_122) | ~v5_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.47/1.37  tff(c_177, plain, (![A_125, B_126, C_127]: (r1_orders_2(A_125, k11_lattice3(A_125, B_126, C_127), B_126) | ~v2_lattice3(A_125) | ~v5_orders_2(A_125) | v2_struct_0(A_125) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125))), inference(resolution, [status(thm)], [c_12, c_169])).
% 2.47/1.37  tff(c_114, plain, (![A_98, B_99, C_100]: (r3_orders_2(A_98, B_99, C_100) | ~r1_orders_2(A_98, B_99, C_100) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.37  tff(c_121, plain, (![A_61, B_99, C_100]: (r3_orders_2(k2_yellow_1(A_61), B_99, C_100) | ~r1_orders_2(k2_yellow_1(A_61), B_99, C_100) | ~m1_subset_1(C_100, A_61) | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1(A_61))) | ~l1_orders_2(k2_yellow_1(A_61)) | ~v3_orders_2(k2_yellow_1(A_61)) | v2_struct_0(k2_yellow_1(A_61)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_114])).
% 2.47/1.37  tff(c_126, plain, (![A_101, B_102, C_103]: (r3_orders_2(k2_yellow_1(A_101), B_102, C_103) | ~r1_orders_2(k2_yellow_1(A_101), B_102, C_103) | ~m1_subset_1(C_103, A_101) | ~m1_subset_1(B_102, A_101) | v2_struct_0(k2_yellow_1(A_101)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_40, c_121])).
% 2.47/1.37  tff(c_130, plain, (![B_102, C_103, A_101]: (r1_tarski(B_102, C_103) | v1_xboole_0(A_101) | ~r1_orders_2(k2_yellow_1(A_101), B_102, C_103) | ~m1_subset_1(C_103, A_101) | ~m1_subset_1(B_102, A_101) | v2_struct_0(k2_yellow_1(A_101)))), inference(resolution, [status(thm)], [c_126, c_59])).
% 2.47/1.37  tff(c_181, plain, (![A_101, B_126, C_127]: (r1_tarski(k11_lattice3(k2_yellow_1(A_101), B_126, C_127), B_126) | v1_xboole_0(A_101) | ~m1_subset_1(B_126, A_101) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_101), B_126, C_127), A_101) | ~v2_lattice3(k2_yellow_1(A_101)) | ~v5_orders_2(k2_yellow_1(A_101)) | v2_struct_0(k2_yellow_1(A_101)) | ~m1_subset_1(C_127, u1_struct_0(k2_yellow_1(A_101))) | ~m1_subset_1(B_126, u1_struct_0(k2_yellow_1(A_101))) | ~l1_orders_2(k2_yellow_1(A_101)))), inference(resolution, [status(thm)], [c_177, c_130])).
% 2.47/1.37  tff(c_190, plain, (![A_131, B_132, C_133]: (r1_tarski(k11_lattice3(k2_yellow_1(A_131), B_132, C_133), B_132) | v1_xboole_0(A_131) | ~m1_subset_1(k11_lattice3(k2_yellow_1(A_131), B_132, C_133), A_131) | ~v2_lattice3(k2_yellow_1(A_131)) | v2_struct_0(k2_yellow_1(A_131)) | ~m1_subset_1(C_133, A_131) | ~m1_subset_1(B_132, A_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_40, c_38, c_181])).
% 2.47/1.37  tff(c_194, plain, (![A_134, B_135, C_136]: (r1_tarski(k11_lattice3(k2_yellow_1(A_134), B_135, C_136), B_135) | v1_xboole_0(A_134) | ~v2_lattice3(k2_yellow_1(A_134)) | v2_struct_0(k2_yellow_1(A_134)) | ~m1_subset_1(C_136, A_134) | ~m1_subset_1(B_135, A_134))), inference(resolution, [status(thm)], [c_112, c_190])).
% 2.47/1.37  tff(c_95, plain, (![A_83, B_84, C_85]: (r1_tarski(A_83, k3_xboole_0(B_84, C_85)) | ~r1_tarski(A_83, C_85) | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_48, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.47/1.37  tff(c_99, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_95, c_48])).
% 2.47/1.37  tff(c_101, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_99])).
% 2.47/1.37  tff(c_197, plain, (v1_xboole_0('#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_194, c_101])).
% 2.47/1.37  tff(c_200, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_54, c_197])).
% 2.47/1.37  tff(c_201, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_200])).
% 2.47/1.37  tff(c_10, plain, (![A_9]: (~v2_struct_0(A_9) | ~v2_lattice3(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.37  tff(c_204, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_201, c_10])).
% 2.47/1.37  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_54, c_204])).
% 2.47/1.37  tff(c_209, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_99])).
% 2.47/1.37  tff(c_320, plain, (v1_xboole_0('#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_317, c_209])).
% 2.47/1.37  tff(c_323, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_54, c_320])).
% 2.47/1.37  tff(c_324, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_323])).
% 2.47/1.37  tff(c_327, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_324, c_10])).
% 2.47/1.37  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_54, c_327])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 50
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 1
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 8
% 2.47/1.37  #Demod        : 82
% 2.47/1.37  #Tautology    : 13
% 2.47/1.37  #SimpNegUnit  : 2
% 2.47/1.37  #BackRed      : 0
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.47/1.37  Preprocessing        : 0.31
% 2.47/1.37  Parsing              : 0.16
% 2.47/1.37  CNF conversion       : 0.03
% 2.47/1.37  Main loop            : 0.27
% 2.47/1.37  Inferencing          : 0.11
% 2.47/1.37  Reduction            : 0.08
% 2.47/1.37  Demodulation         : 0.06
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.05
% 2.47/1.37  Abstraction          : 0.01
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.62
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
