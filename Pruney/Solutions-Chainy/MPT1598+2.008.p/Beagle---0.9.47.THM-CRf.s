%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:22 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 507 expanded)
%              Number of leaves         :   39 ( 210 expanded)
%              Depth                    :   14
%              Number of atoms          :  401 (1543 expanded)
%              Number of equality atoms :   15 ( 244 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

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

tff(f_126,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

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

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_44,plain,(
    ! [A_64] : u1_struct_0(k2_yellow_1(A_64)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_61,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_58,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38,plain,(
    ! [A_62] : v5_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_61] : l1_orders_2(k2_yellow_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_320,plain,(
    ! [A_165,B_166,C_167] :
      ( k13_lattice3(A_165,B_166,C_167) = k10_lattice3(A_165,B_166,C_167)
      | ~ m1_subset_1(C_167,u1_struct_0(A_165))
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v1_lattice3(A_165)
      | ~ v5_orders_2(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_327,plain,(
    ! [A_64,B_166,C_167] :
      ( k13_lattice3(k2_yellow_1(A_64),B_166,C_167) = k10_lattice3(k2_yellow_1(A_64),B_166,C_167)
      | ~ m1_subset_1(C_167,A_64)
      | ~ m1_subset_1(B_166,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v1_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_320])).

tff(c_332,plain,(
    ! [A_168,B_169,C_170] :
      ( k13_lattice3(k2_yellow_1(A_168),B_169,C_170) = k10_lattice3(k2_yellow_1(A_168),B_169,C_170)
      | ~ m1_subset_1(C_170,A_168)
      | ~ m1_subset_1(B_169,A_168)
      | ~ v1_lattice3(k2_yellow_1(A_168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_327])).

tff(c_336,plain,(
    ! [B_171,C_172] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_171,C_172) = k10_lattice3(k2_yellow_1('#skF_2'),B_171,C_172)
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_332])).

tff(c_306,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1(k13_lattice3(A_153,B_154,C_155),u1_struct_0(A_153))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v1_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,(
    ! [A_64,B_154,C_155] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_64),B_154,C_155),A_64)
      | ~ m1_subset_1(C_155,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_154,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v1_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_306])).

tff(c_311,plain,(
    ! [A_64,B_154,C_155] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_64),B_154,C_155),A_64)
      | ~ m1_subset_1(C_155,A_64)
      | ~ m1_subset_1(B_154,A_64)
      | ~ v1_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_309])).

tff(c_342,plain,(
    ! [B_171,C_172] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_171,C_172),'#skF_2')
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_311])).

tff(c_351,plain,(
    ! [B_171,C_172] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_171,C_172),'#skF_2')
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_342])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_335,plain,(
    ! [B_169,C_170] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_169,C_170) = k10_lattice3(k2_yellow_1('#skF_2'),B_169,C_170)
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_332])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k13_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v1_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_378,plain,(
    ! [A_181,B_182,C_183] :
      ( r1_orders_2(A_181,B_182,k13_lattice3(A_181,B_182,C_183))
      | ~ m1_subset_1(k13_lattice3(A_181,B_182,C_183),u1_struct_0(A_181))
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v1_lattice3(A_181)
      | ~ v5_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_395,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_orders_2(A_187,B_188,k13_lattice3(A_187,B_188,C_189))
      | ~ m1_subset_1(C_189,u1_struct_0(A_187))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | ~ v1_lattice3(A_187)
      | ~ v5_orders_2(A_187) ) ),
    inference(resolution,[status(thm)],[c_10,c_378])).

tff(c_402,plain,(
    ! [B_169,C_170] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_169,k10_lattice3(k2_yellow_1('#skF_2'),B_169,C_170))
      | ~ m1_subset_1(C_170,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_395])).

tff(c_408,plain,(
    ! [B_190,C_191] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_190,k10_lattice3(k2_yellow_1('#skF_2'),B_190,C_191))
      | ~ m1_subset_1(C_191,'#skF_2')
      | ~ m1_subset_1(B_190,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_402])).

tff(c_34,plain,(
    ! [A_62] : v3_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_355,plain,(
    ! [A_173,B_174,C_175] :
      ( r3_orders_2(A_173,B_174,C_175)
      | ~ r1_orders_2(A_173,B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173)
      | ~ v3_orders_2(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_362,plain,(
    ! [A_64,B_174,C_175] :
      ( r3_orders_2(k2_yellow_1(A_64),B_174,C_175)
      | ~ r1_orders_2(k2_yellow_1(A_64),B_174,C_175)
      | ~ m1_subset_1(C_175,A_64)
      | ~ m1_subset_1(B_174,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v3_orders_2(k2_yellow_1(A_64))
      | v2_struct_0(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_355])).

tff(c_368,plain,(
    ! [A_178,B_179,C_180] :
      ( r3_orders_2(k2_yellow_1(A_178),B_179,C_180)
      | ~ r1_orders_2(k2_yellow_1(A_178),B_179,C_180)
      | ~ m1_subset_1(C_180,A_178)
      | ~ m1_subset_1(B_179,A_178)
      | v2_struct_0(k2_yellow_1(A_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_362])).

tff(c_50,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_69,u1_struct_0(k2_yellow_1(A_65)))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,A_65)
      | ~ m1_subset_1(B_69,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_50])).

tff(c_377,plain,(
    ! [B_179,C_180,A_178] :
      ( r1_tarski(B_179,C_180)
      | v1_xboole_0(A_178)
      | ~ r1_orders_2(k2_yellow_1(A_178),B_179,C_180)
      | ~ m1_subset_1(C_180,A_178)
      | ~ m1_subset_1(B_179,A_178)
      | v2_struct_0(k2_yellow_1(A_178)) ) ),
    inference(resolution,[status(thm)],[c_368,c_63])).

tff(c_411,plain,(
    ! [B_190,C_191] :
      ( r1_tarski(B_190,k10_lattice3(k2_yellow_1('#skF_2'),B_190,C_191))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_191,'#skF_2')
      | ~ m1_subset_1(B_190,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_408,c_377])).

tff(c_414,plain,(
    ! [B_190,C_191] :
      ( r1_tarski(B_190,k10_lattice3(k2_yellow_1('#skF_2'),B_190,C_191))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_191,'#skF_2')
      | ~ m1_subset_1(B_190,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_411])).

tff(c_425,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_42,plain,(
    ! [A_63] :
      ( ~ v2_struct_0(k2_yellow_1(A_63))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_440,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_425,c_42])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_440])).

tff(c_446,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_463,plain,(
    ! [A_204,C_205,B_206] :
      ( r1_orders_2(A_204,C_205,k13_lattice3(A_204,B_206,C_205))
      | ~ m1_subset_1(k13_lattice3(A_204,B_206,C_205),u1_struct_0(A_204))
      | ~ m1_subset_1(C_205,u1_struct_0(A_204))
      | ~ m1_subset_1(B_206,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ v1_lattice3(A_204)
      | ~ v5_orders_2(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_475,plain,(
    ! [A_207,C_208,B_209] :
      ( r1_orders_2(A_207,C_208,k13_lattice3(A_207,B_209,C_208))
      | ~ m1_subset_1(C_208,u1_struct_0(A_207))
      | ~ m1_subset_1(B_209,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v1_lattice3(A_207)
      | ~ v5_orders_2(A_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_463])).

tff(c_482,plain,(
    ! [C_170,B_169] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_170,k10_lattice3(k2_yellow_1('#skF_2'),B_169,C_170))
      | ~ m1_subset_1(C_170,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_475])).

tff(c_488,plain,(
    ! [C_210,B_211] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_210,k10_lattice3(k2_yellow_1('#skF_2'),B_211,C_210))
      | ~ m1_subset_1(C_210,'#skF_2')
      | ~ m1_subset_1(B_211,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_482])).

tff(c_491,plain,(
    ! [C_210,B_211] :
      ( r1_tarski(C_210,k10_lattice3(k2_yellow_1('#skF_2'),B_211,C_210))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_211,C_210),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_210,'#skF_2')
      | ~ m1_subset_1(B_211,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_488,c_377])).

tff(c_495,plain,(
    ! [C_212,B_213] :
      ( r1_tarski(C_212,k10_lattice3(k2_yellow_1('#skF_2'),B_213,C_212))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_213,C_212),'#skF_2')
      | ~ m1_subset_1(C_212,'#skF_2')
      | ~ m1_subset_1(B_213,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_60,c_491])).

tff(c_119,plain,(
    ! [A_101,B_102,C_103] :
      ( k13_lattice3(A_101,B_102,C_103) = k10_lattice3(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v1_lattice3(A_101)
      | ~ v5_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    ! [A_64,B_102,C_103] :
      ( k13_lattice3(k2_yellow_1(A_64),B_102,C_103) = k10_lattice3(k2_yellow_1(A_64),B_102,C_103)
      | ~ m1_subset_1(C_103,A_64)
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v1_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_131,plain,(
    ! [A_104,B_105,C_106] :
      ( k13_lattice3(k2_yellow_1(A_104),B_105,C_106) = k10_lattice3(k2_yellow_1(A_104),B_105,C_106)
      | ~ m1_subset_1(C_106,A_104)
      | ~ m1_subset_1(B_105,A_104)
      | ~ v1_lattice3(k2_yellow_1(A_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_126])).

tff(c_135,plain,(
    ! [B_107,C_108] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_107,C_108) = k10_lattice3(k2_yellow_1('#skF_2'),B_107,C_108)
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_112,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k13_lattice3(A_95,B_96,C_97),u1_struct_0(A_95))
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v1_lattice3(A_95)
      | ~ v5_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [A_64,B_96,C_97] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_64),B_96,C_97),A_64)
      | ~ m1_subset_1(C_97,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v1_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_117,plain,(
    ! [A_64,B_96,C_97] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_64),B_96,C_97),A_64)
      | ~ m1_subset_1(C_97,A_64)
      | ~ m1_subset_1(B_96,A_64)
      | ~ v1_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_115])).

tff(c_141,plain,(
    ! [B_107,C_108] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_107,C_108),'#skF_2')
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_117])).

tff(c_150,plain,(
    ! [B_107,C_108] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_107,C_108),'#skF_2')
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_141])).

tff(c_134,plain,(
    ! [B_105,C_106] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_105,C_106) = k10_lattice3(k2_yellow_1('#skF_2'),B_105,C_106)
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_231,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_orders_2(A_136,C_137,k13_lattice3(A_136,B_138,C_137))
      | ~ m1_subset_1(k13_lattice3(A_136,B_138,C_137),u1_struct_0(A_136))
      | ~ m1_subset_1(C_137,u1_struct_0(A_136))
      | ~ m1_subset_1(B_138,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v1_lattice3(A_136)
      | ~ v5_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_243,plain,(
    ! [A_139,C_140,B_141] :
      ( r1_orders_2(A_139,C_140,k13_lattice3(A_139,B_141,C_140))
      | ~ m1_subset_1(C_140,u1_struct_0(A_139))
      | ~ m1_subset_1(B_141,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v1_lattice3(A_139)
      | ~ v5_orders_2(A_139) ) ),
    inference(resolution,[status(thm)],[c_10,c_231])).

tff(c_250,plain,(
    ! [C_106,B_105] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_106,k10_lattice3(k2_yellow_1('#skF_2'),B_105,C_106))
      | ~ m1_subset_1(C_106,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_243])).

tff(c_256,plain,(
    ! [C_142,B_143] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_142,k10_lattice3(k2_yellow_1('#skF_2'),B_143,C_142))
      | ~ m1_subset_1(C_142,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_250])).

tff(c_155,plain,(
    ! [A_111,B_112,C_113] :
      ( r3_orders_2(A_111,B_112,C_113)
      | ~ r1_orders_2(A_111,B_112,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [A_64,B_112,C_113] :
      ( r3_orders_2(k2_yellow_1(A_64),B_112,C_113)
      | ~ r1_orders_2(k2_yellow_1(A_64),B_112,C_113)
      | ~ m1_subset_1(C_113,A_64)
      | ~ m1_subset_1(B_112,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v3_orders_2(k2_yellow_1(A_64))
      | v2_struct_0(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_155])).

tff(c_167,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(k2_yellow_1(A_114),B_115,C_116)
      | ~ r1_orders_2(k2_yellow_1(A_114),B_115,C_116)
      | ~ m1_subset_1(C_116,A_114)
      | ~ m1_subset_1(B_115,A_114)
      | v2_struct_0(k2_yellow_1(A_114)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_162])).

tff(c_171,plain,(
    ! [B_115,C_116,A_114] :
      ( r1_tarski(B_115,C_116)
      | v1_xboole_0(A_114)
      | ~ r1_orders_2(k2_yellow_1(A_114),B_115,C_116)
      | ~ m1_subset_1(C_116,A_114)
      | ~ m1_subset_1(B_115,A_114)
      | v2_struct_0(k2_yellow_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_167,c_63])).

tff(c_259,plain,(
    ! [C_142,B_143] :
      ( r1_tarski(C_142,k10_lattice3(k2_yellow_1('#skF_2'),B_143,C_142))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_143,C_142),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_142,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_256,c_171])).

tff(c_262,plain,(
    ! [C_142,B_143] :
      ( r1_tarski(C_142,k10_lattice3(k2_yellow_1('#skF_2'),B_143,C_142))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_143,C_142),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_142,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_259])).

tff(c_273,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_276,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_273,c_42])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_276])).

tff(c_282,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_189,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_orders_2(A_126,B_127,k13_lattice3(A_126,B_127,C_128))
      | ~ m1_subset_1(k13_lattice3(A_126,B_127,C_128),u1_struct_0(A_126))
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v1_lattice3(A_126)
      | ~ v5_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_201,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_orders_2(A_129,B_130,k13_lattice3(A_129,B_130,C_131))
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v1_lattice3(A_129)
      | ~ v5_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_208,plain,(
    ! [B_105,C_106] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_105,k10_lattice3(k2_yellow_1('#skF_2'),B_105,C_106))
      | ~ m1_subset_1(C_106,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_201])).

tff(c_214,plain,(
    ! [B_132,C_133] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_132,k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_133))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_208])).

tff(c_217,plain,(
    ! [B_132,C_133] :
      ( r1_tarski(B_132,k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_133))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_214,c_171])).

tff(c_220,plain,(
    ! [B_132,C_133] :
      ( r1_tarski(B_132,k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_133))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_217])).

tff(c_285,plain,(
    ! [B_148,C_149] :
      ( r1_tarski(B_148,k10_lattice3(k2_yellow_1('#skF_2'),B_148,C_149))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_148,C_149),'#skF_2')
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_220])).

tff(c_100,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(k2_xboole_0(A_86,C_87),B_88)
      | ~ r1_tarski(C_87,B_88)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_104,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_100,c_52])).

tff(c_106,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_288,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_106])).

tff(c_291,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_288])).

tff(c_294,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_291])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_294])).

tff(c_299,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_498,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_495,c_299])).

tff(c_501,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_498])).

tff(c_516,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_351,c_501])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.44  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.44  
% 2.83/1.44  %Foreground sorts:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Background operators:
% 2.83/1.44  
% 2.83/1.44  
% 2.83/1.44  %Foreground operators:
% 2.83/1.44  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.83/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.44  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.83/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.44  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 2.83/1.44  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.44  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.83/1.44  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.83/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.44  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.83/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.83/1.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.83/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.83/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.44  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.83/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.44  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.83/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.83/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.44  
% 3.11/1.46  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.11/1.46  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 3.11/1.46  tff(f_114, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.11/1.46  tff(f_106, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.11/1.46  tff(f_72, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.11/1.46  tff(f_60, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 3.11/1.46  tff(f_102, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 3.11/1.46  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.11/1.46  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.11/1.46  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.11/1.46  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.11/1.46  tff(c_44, plain, (![A_64]: (u1_struct_0(k2_yellow_1(A_64))=A_64)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.11/1.46  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.46  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 3.11/1.46  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.46  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 3.11/1.46  tff(c_58, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.46  tff(c_38, plain, (![A_62]: (v5_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.46  tff(c_30, plain, (![A_61]: (l1_orders_2(k2_yellow_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.46  tff(c_320, plain, (![A_165, B_166, C_167]: (k13_lattice3(A_165, B_166, C_167)=k10_lattice3(A_165, B_166, C_167) | ~m1_subset_1(C_167, u1_struct_0(A_165)) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~v1_lattice3(A_165) | ~v5_orders_2(A_165))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.46  tff(c_327, plain, (![A_64, B_166, C_167]: (k13_lattice3(k2_yellow_1(A_64), B_166, C_167)=k10_lattice3(k2_yellow_1(A_64), B_166, C_167) | ~m1_subset_1(C_167, A_64) | ~m1_subset_1(B_166, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v1_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_320])).
% 3.11/1.46  tff(c_332, plain, (![A_168, B_169, C_170]: (k13_lattice3(k2_yellow_1(A_168), B_169, C_170)=k10_lattice3(k2_yellow_1(A_168), B_169, C_170) | ~m1_subset_1(C_170, A_168) | ~m1_subset_1(B_169, A_168) | ~v1_lattice3(k2_yellow_1(A_168)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_327])).
% 3.11/1.46  tff(c_336, plain, (![B_171, C_172]: (k13_lattice3(k2_yellow_1('#skF_2'), B_171, C_172)=k10_lattice3(k2_yellow_1('#skF_2'), B_171, C_172) | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_332])).
% 3.11/1.46  tff(c_306, plain, (![A_153, B_154, C_155]: (m1_subset_1(k13_lattice3(A_153, B_154, C_155), u1_struct_0(A_153)) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v1_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.46  tff(c_309, plain, (![A_64, B_154, C_155]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_64), B_154, C_155), A_64) | ~m1_subset_1(C_155, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_154, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v1_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_306])).
% 3.11/1.46  tff(c_311, plain, (![A_64, B_154, C_155]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_64), B_154, C_155), A_64) | ~m1_subset_1(C_155, A_64) | ~m1_subset_1(B_154, A_64) | ~v1_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_309])).
% 3.11/1.46  tff(c_342, plain, (![B_171, C_172]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_171, C_172), '#skF_2') | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_311])).
% 3.11/1.46  tff(c_351, plain, (![B_171, C_172]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_171, C_172), '#skF_2') | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_342])).
% 3.11/1.46  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.46  tff(c_335, plain, (![B_169, C_170]: (k13_lattice3(k2_yellow_1('#skF_2'), B_169, C_170)=k10_lattice3(k2_yellow_1('#skF_2'), B_169, C_170) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_332])).
% 3.11/1.46  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k13_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v1_lattice3(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.46  tff(c_378, plain, (![A_181, B_182, C_183]: (r1_orders_2(A_181, B_182, k13_lattice3(A_181, B_182, C_183)) | ~m1_subset_1(k13_lattice3(A_181, B_182, C_183), u1_struct_0(A_181)) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v1_lattice3(A_181) | ~v5_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.46  tff(c_395, plain, (![A_187, B_188, C_189]: (r1_orders_2(A_187, B_188, k13_lattice3(A_187, B_188, C_189)) | ~m1_subset_1(C_189, u1_struct_0(A_187)) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l1_orders_2(A_187) | ~v1_lattice3(A_187) | ~v5_orders_2(A_187))), inference(resolution, [status(thm)], [c_10, c_378])).
% 3.11/1.46  tff(c_402, plain, (![B_169, C_170]: (r1_orders_2(k2_yellow_1('#skF_2'), B_169, k10_lattice3(k2_yellow_1('#skF_2'), B_169, C_170)) | ~m1_subset_1(C_170, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_395])).
% 3.11/1.46  tff(c_408, plain, (![B_190, C_191]: (r1_orders_2(k2_yellow_1('#skF_2'), B_190, k10_lattice3(k2_yellow_1('#skF_2'), B_190, C_191)) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_402])).
% 3.11/1.46  tff(c_34, plain, (![A_62]: (v3_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.46  tff(c_355, plain, (![A_173, B_174, C_175]: (r3_orders_2(A_173, B_174, C_175) | ~r1_orders_2(A_173, B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v3_orders_2(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.46  tff(c_362, plain, (![A_64, B_174, C_175]: (r3_orders_2(k2_yellow_1(A_64), B_174, C_175) | ~r1_orders_2(k2_yellow_1(A_64), B_174, C_175) | ~m1_subset_1(C_175, A_64) | ~m1_subset_1(B_174, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_355])).
% 3.11/1.46  tff(c_368, plain, (![A_178, B_179, C_180]: (r3_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~r1_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~m1_subset_1(C_180, A_178) | ~m1_subset_1(B_179, A_178) | v2_struct_0(k2_yellow_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_362])).
% 3.11/1.46  tff(c_50, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_69, u1_struct_0(k2_yellow_1(A_65))) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.11/1.46  tff(c_63, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, A_65) | ~m1_subset_1(B_69, A_65) | v1_xboole_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 3.11/1.46  tff(c_377, plain, (![B_179, C_180, A_178]: (r1_tarski(B_179, C_180) | v1_xboole_0(A_178) | ~r1_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~m1_subset_1(C_180, A_178) | ~m1_subset_1(B_179, A_178) | v2_struct_0(k2_yellow_1(A_178)))), inference(resolution, [status(thm)], [c_368, c_63])).
% 3.11/1.46  tff(c_411, plain, (![B_190, C_191]: (r1_tarski(B_190, k10_lattice3(k2_yellow_1('#skF_2'), B_190, C_191)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(resolution, [status(thm)], [c_408, c_377])).
% 3.11/1.46  tff(c_414, plain, (![B_190, C_191]: (r1_tarski(B_190, k10_lattice3(k2_yellow_1('#skF_2'), B_190, C_191)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_411])).
% 3.11/1.46  tff(c_425, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_414])).
% 3.11/1.46  tff(c_42, plain, (![A_63]: (~v2_struct_0(k2_yellow_1(A_63)) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.11/1.46  tff(c_440, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_425, c_42])).
% 3.11/1.46  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_440])).
% 3.11/1.46  tff(c_446, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_414])).
% 3.11/1.46  tff(c_463, plain, (![A_204, C_205, B_206]: (r1_orders_2(A_204, C_205, k13_lattice3(A_204, B_206, C_205)) | ~m1_subset_1(k13_lattice3(A_204, B_206, C_205), u1_struct_0(A_204)) | ~m1_subset_1(C_205, u1_struct_0(A_204)) | ~m1_subset_1(B_206, u1_struct_0(A_204)) | ~l1_orders_2(A_204) | ~v1_lattice3(A_204) | ~v5_orders_2(A_204))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.46  tff(c_475, plain, (![A_207, C_208, B_209]: (r1_orders_2(A_207, C_208, k13_lattice3(A_207, B_209, C_208)) | ~m1_subset_1(C_208, u1_struct_0(A_207)) | ~m1_subset_1(B_209, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v1_lattice3(A_207) | ~v5_orders_2(A_207))), inference(resolution, [status(thm)], [c_10, c_463])).
% 3.11/1.46  tff(c_482, plain, (![C_170, B_169]: (r1_orders_2(k2_yellow_1('#skF_2'), C_170, k10_lattice3(k2_yellow_1('#skF_2'), B_169, C_170)) | ~m1_subset_1(C_170, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_475])).
% 3.11/1.46  tff(c_488, plain, (![C_210, B_211]: (r1_orders_2(k2_yellow_1('#skF_2'), C_210, k10_lattice3(k2_yellow_1('#skF_2'), B_211, C_210)) | ~m1_subset_1(C_210, '#skF_2') | ~m1_subset_1(B_211, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_482])).
% 3.11/1.46  tff(c_491, plain, (![C_210, B_211]: (r1_tarski(C_210, k10_lattice3(k2_yellow_1('#skF_2'), B_211, C_210)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_211, C_210), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_210, '#skF_2') | ~m1_subset_1(B_211, '#skF_2'))), inference(resolution, [status(thm)], [c_488, c_377])).
% 3.11/1.46  tff(c_495, plain, (![C_212, B_213]: (r1_tarski(C_212, k10_lattice3(k2_yellow_1('#skF_2'), B_213, C_212)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_213, C_212), '#skF_2') | ~m1_subset_1(C_212, '#skF_2') | ~m1_subset_1(B_213, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_446, c_60, c_491])).
% 3.11/1.46  tff(c_119, plain, (![A_101, B_102, C_103]: (k13_lattice3(A_101, B_102, C_103)=k10_lattice3(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v1_lattice3(A_101) | ~v5_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.46  tff(c_126, plain, (![A_64, B_102, C_103]: (k13_lattice3(k2_yellow_1(A_64), B_102, C_103)=k10_lattice3(k2_yellow_1(A_64), B_102, C_103) | ~m1_subset_1(C_103, A_64) | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v1_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_119])).
% 3.11/1.46  tff(c_131, plain, (![A_104, B_105, C_106]: (k13_lattice3(k2_yellow_1(A_104), B_105, C_106)=k10_lattice3(k2_yellow_1(A_104), B_105, C_106) | ~m1_subset_1(C_106, A_104) | ~m1_subset_1(B_105, A_104) | ~v1_lattice3(k2_yellow_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_126])).
% 3.11/1.46  tff(c_135, plain, (![B_107, C_108]: (k13_lattice3(k2_yellow_1('#skF_2'), B_107, C_108)=k10_lattice3(k2_yellow_1('#skF_2'), B_107, C_108) | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 3.11/1.46  tff(c_112, plain, (![A_95, B_96, C_97]: (m1_subset_1(k13_lattice3(A_95, B_96, C_97), u1_struct_0(A_95)) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v1_lattice3(A_95) | ~v5_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.46  tff(c_115, plain, (![A_64, B_96, C_97]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_64), B_96, C_97), A_64) | ~m1_subset_1(C_97, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v1_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_112])).
% 3.11/1.46  tff(c_117, plain, (![A_64, B_96, C_97]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_64), B_96, C_97), A_64) | ~m1_subset_1(C_97, A_64) | ~m1_subset_1(B_96, A_64) | ~v1_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_115])).
% 3.11/1.46  tff(c_141, plain, (![B_107, C_108]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_107, C_108), '#skF_2') | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_117])).
% 3.11/1.46  tff(c_150, plain, (![B_107, C_108]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_107, C_108), '#skF_2') | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_141])).
% 3.11/1.46  tff(c_134, plain, (![B_105, C_106]: (k13_lattice3(k2_yellow_1('#skF_2'), B_105, C_106)=k10_lattice3(k2_yellow_1('#skF_2'), B_105, C_106) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 3.11/1.46  tff(c_231, plain, (![A_136, C_137, B_138]: (r1_orders_2(A_136, C_137, k13_lattice3(A_136, B_138, C_137)) | ~m1_subset_1(k13_lattice3(A_136, B_138, C_137), u1_struct_0(A_136)) | ~m1_subset_1(C_137, u1_struct_0(A_136)) | ~m1_subset_1(B_138, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v1_lattice3(A_136) | ~v5_orders_2(A_136))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.46  tff(c_243, plain, (![A_139, C_140, B_141]: (r1_orders_2(A_139, C_140, k13_lattice3(A_139, B_141, C_140)) | ~m1_subset_1(C_140, u1_struct_0(A_139)) | ~m1_subset_1(B_141, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v1_lattice3(A_139) | ~v5_orders_2(A_139))), inference(resolution, [status(thm)], [c_10, c_231])).
% 3.11/1.46  tff(c_250, plain, (![C_106, B_105]: (r1_orders_2(k2_yellow_1('#skF_2'), C_106, k10_lattice3(k2_yellow_1('#skF_2'), B_105, C_106)) | ~m1_subset_1(C_106, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_243])).
% 3.11/1.46  tff(c_256, plain, (![C_142, B_143]: (r1_orders_2(k2_yellow_1('#skF_2'), C_142, k10_lattice3(k2_yellow_1('#skF_2'), B_143, C_142)) | ~m1_subset_1(C_142, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_250])).
% 3.11/1.46  tff(c_155, plain, (![A_111, B_112, C_113]: (r3_orders_2(A_111, B_112, C_113) | ~r1_orders_2(A_111, B_112, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.46  tff(c_162, plain, (![A_64, B_112, C_113]: (r3_orders_2(k2_yellow_1(A_64), B_112, C_113) | ~r1_orders_2(k2_yellow_1(A_64), B_112, C_113) | ~m1_subset_1(C_113, A_64) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_155])).
% 3.11/1.46  tff(c_167, plain, (![A_114, B_115, C_116]: (r3_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~r1_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~m1_subset_1(C_116, A_114) | ~m1_subset_1(B_115, A_114) | v2_struct_0(k2_yellow_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_162])).
% 3.11/1.46  tff(c_171, plain, (![B_115, C_116, A_114]: (r1_tarski(B_115, C_116) | v1_xboole_0(A_114) | ~r1_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~m1_subset_1(C_116, A_114) | ~m1_subset_1(B_115, A_114) | v2_struct_0(k2_yellow_1(A_114)))), inference(resolution, [status(thm)], [c_167, c_63])).
% 3.11/1.46  tff(c_259, plain, (![C_142, B_143]: (r1_tarski(C_142, k10_lattice3(k2_yellow_1('#skF_2'), B_143, C_142)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_143, C_142), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_142, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(resolution, [status(thm)], [c_256, c_171])).
% 3.11/1.46  tff(c_262, plain, (![C_142, B_143]: (r1_tarski(C_142, k10_lattice3(k2_yellow_1('#skF_2'), B_143, C_142)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_143, C_142), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_142, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_259])).
% 3.11/1.46  tff(c_273, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_262])).
% 3.11/1.46  tff(c_276, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_273, c_42])).
% 3.11/1.46  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_276])).
% 3.11/1.46  tff(c_282, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_262])).
% 3.11/1.46  tff(c_189, plain, (![A_126, B_127, C_128]: (r1_orders_2(A_126, B_127, k13_lattice3(A_126, B_127, C_128)) | ~m1_subset_1(k13_lattice3(A_126, B_127, C_128), u1_struct_0(A_126)) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v1_lattice3(A_126) | ~v5_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.46  tff(c_201, plain, (![A_129, B_130, C_131]: (r1_orders_2(A_129, B_130, k13_lattice3(A_129, B_130, C_131)) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v1_lattice3(A_129) | ~v5_orders_2(A_129))), inference(resolution, [status(thm)], [c_10, c_189])).
% 3.11/1.46  tff(c_208, plain, (![B_105, C_106]: (r1_orders_2(k2_yellow_1('#skF_2'), B_105, k10_lattice3(k2_yellow_1('#skF_2'), B_105, C_106)) | ~m1_subset_1(C_106, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_201])).
% 3.11/1.46  tff(c_214, plain, (![B_132, C_133]: (r1_orders_2(k2_yellow_1('#skF_2'), B_132, k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_133)) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_208])).
% 3.11/1.46  tff(c_217, plain, (![B_132, C_133]: (r1_tarski(B_132, k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_133)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(resolution, [status(thm)], [c_214, c_171])).
% 3.11/1.46  tff(c_220, plain, (![B_132, C_133]: (r1_tarski(B_132, k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_133)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_217])).
% 3.11/1.46  tff(c_285, plain, (![B_148, C_149]: (r1_tarski(B_148, k10_lattice3(k2_yellow_1('#skF_2'), B_148, C_149)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_148, C_149), '#skF_2') | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_282, c_220])).
% 3.11/1.46  tff(c_100, plain, (![A_86, C_87, B_88]: (r1_tarski(k2_xboole_0(A_86, C_87), B_88) | ~r1_tarski(C_87, B_88) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.46  tff(c_52, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.46  tff(c_104, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_52])).
% 3.11/1.46  tff(c_106, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_104])).
% 3.11/1.46  tff(c_288, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_285, c_106])).
% 3.11/1.46  tff(c_291, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_288])).
% 3.11/1.46  tff(c_294, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_150, c_291])).
% 3.11/1.46  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_294])).
% 3.11/1.46  tff(c_299, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_104])).
% 3.11/1.46  tff(c_498, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_495, c_299])).
% 3.11/1.46  tff(c_501, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_498])).
% 3.11/1.46  tff(c_516, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_351, c_501])).
% 3.11/1.46  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_516])).
% 3.11/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  Inference rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Ref     : 0
% 3.11/1.46  #Sup     : 86
% 3.11/1.46  #Fact    : 0
% 3.11/1.46  #Define  : 0
% 3.11/1.46  #Split   : 3
% 3.11/1.46  #Chain   : 0
% 3.11/1.46  #Close   : 0
% 3.11/1.46  
% 3.11/1.46  Ordering : KBO
% 3.11/1.46  
% 3.11/1.46  Simplification rules
% 3.11/1.46  ----------------------
% 3.11/1.46  #Subsume      : 11
% 3.11/1.46  #Demod        : 158
% 3.11/1.46  #Tautology    : 18
% 3.11/1.46  #SimpNegUnit  : 11
% 3.11/1.46  #BackRed      : 0
% 3.11/1.46  
% 3.11/1.46  #Partial instantiations: 0
% 3.11/1.46  #Strategies tried      : 1
% 3.11/1.46  
% 3.11/1.46  Timing (in seconds)
% 3.11/1.46  ----------------------
% 3.11/1.47  Preprocessing        : 0.34
% 3.11/1.47  Parsing              : 0.18
% 3.11/1.47  CNF conversion       : 0.03
% 3.11/1.47  Main loop            : 0.31
% 3.11/1.47  Inferencing          : 0.12
% 3.11/1.47  Reduction            : 0.10
% 3.11/1.47  Demodulation         : 0.07
% 3.11/1.47  BG Simplification    : 0.02
% 3.11/1.47  Subsumption          : 0.05
% 3.11/1.47  Abstraction          : 0.02
% 3.11/1.47  MUC search           : 0.00
% 3.11/1.47  Cooper               : 0.00
% 3.11/1.47  Total                : 0.70
% 3.11/1.47  Index Insertion      : 0.00
% 3.11/1.47  Index Deletion       : 0.00
% 3.11/1.47  Index Matching       : 0.00
% 3.11/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
