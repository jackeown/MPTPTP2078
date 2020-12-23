%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 2.68s
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
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

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

tff(f_126,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

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
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

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
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

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
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38,plain,(
    ! [A_62] : v5_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_61] : l1_orders_2(k2_yellow_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_320,plain,(
    ! [A_165,B_166,C_167] :
      ( k12_lattice3(A_165,B_166,C_167) = k11_lattice3(A_165,B_166,C_167)
      | ~ m1_subset_1(C_167,u1_struct_0(A_165))
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v2_lattice3(A_165)
      | ~ v5_orders_2(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_327,plain,(
    ! [A_64,B_166,C_167] :
      ( k12_lattice3(k2_yellow_1(A_64),B_166,C_167) = k11_lattice3(k2_yellow_1(A_64),B_166,C_167)
      | ~ m1_subset_1(C_167,A_64)
      | ~ m1_subset_1(B_166,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_320])).

tff(c_332,plain,(
    ! [A_168,B_169,C_170] :
      ( k12_lattice3(k2_yellow_1(A_168),B_169,C_170) = k11_lattice3(k2_yellow_1(A_168),B_169,C_170)
      | ~ m1_subset_1(C_170,A_168)
      | ~ m1_subset_1(B_169,A_168)
      | ~ v2_lattice3(k2_yellow_1(A_168)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_327])).

tff(c_336,plain,(
    ! [B_171,C_172] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_171,C_172) = k11_lattice3(k2_yellow_1('#skF_2'),B_171,C_172)
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_332])).

tff(c_306,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1(k12_lattice3(A_153,B_154,C_155),u1_struct_0(A_153))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v2_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,(
    ! [A_64,B_154,C_155] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_154,C_155),A_64)
      | ~ m1_subset_1(C_155,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_154,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_306])).

tff(c_311,plain,(
    ! [A_64,B_154,C_155] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_154,C_155),A_64)
      | ~ m1_subset_1(C_155,A_64)
      | ~ m1_subset_1(B_154,A_64)
      | ~ v2_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_309])).

tff(c_342,plain,(
    ! [B_171,C_172] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_171,C_172),'#skF_2')
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_311])).

tff(c_351,plain,(
    ! [B_171,C_172] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_171,C_172),'#skF_2')
      | ~ m1_subset_1(C_172,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_342])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_335,plain,(
    ! [B_169,C_170] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_169,C_170) = k11_lattice3(k2_yellow_1('#skF_2'),B_169,C_170)
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_332])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k12_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v2_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_378,plain,(
    ! [A_181,B_182,C_183] :
      ( r1_orders_2(A_181,k12_lattice3(A_181,B_182,C_183),B_182)
      | ~ m1_subset_1(k12_lattice3(A_181,B_182,C_183),u1_struct_0(A_181))
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v2_lattice3(A_181)
      | ~ v5_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_395,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_orders_2(A_187,k12_lattice3(A_187,B_188,C_189),B_188)
      | ~ m1_subset_1(C_189,u1_struct_0(A_187))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | ~ v2_lattice3(A_187)
      | ~ v5_orders_2(A_187) ) ),
    inference(resolution,[status(thm)],[c_10,c_378])).

tff(c_402,plain,(
    ! [B_169,C_170] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_169,C_170),B_169)
      | ~ m1_subset_1(C_170,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_395])).

tff(c_408,plain,(
    ! [B_190,C_191] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),B_190)
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
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),B_190)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_191,'#skF_2')
      | ~ m1_subset_1(B_190,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_408,c_377])).

tff(c_414,plain,(
    ! [B_190,C_191] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),B_190)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_190,C_191),'#skF_2')
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
    ! [A_204,B_205,C_206] :
      ( r1_orders_2(A_204,k12_lattice3(A_204,B_205,C_206),C_206)
      | ~ m1_subset_1(k12_lattice3(A_204,B_205,C_206),u1_struct_0(A_204))
      | ~ m1_subset_1(C_206,u1_struct_0(A_204))
      | ~ m1_subset_1(B_205,u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ v2_lattice3(A_204)
      | ~ v5_orders_2(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_475,plain,(
    ! [A_207,B_208,C_209] :
      ( r1_orders_2(A_207,k12_lattice3(A_207,B_208,C_209),C_209)
      | ~ m1_subset_1(C_209,u1_struct_0(A_207))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l1_orders_2(A_207)
      | ~ v2_lattice3(A_207)
      | ~ v5_orders_2(A_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_463])).

tff(c_482,plain,(
    ! [B_169,C_170] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_169,C_170),C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_475])).

tff(c_488,plain,(
    ! [B_210,C_211] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_210,C_211),C_211)
      | ~ m1_subset_1(C_211,'#skF_2')
      | ~ m1_subset_1(B_210,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_482])).

tff(c_491,plain,(
    ! [B_210,C_211] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_210,C_211),C_211)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_210,C_211),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_211,'#skF_2')
      | ~ m1_subset_1(B_210,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_488,c_377])).

tff(c_495,plain,(
    ! [B_212,C_213] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_212,C_213),C_213)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_212,C_213),'#skF_2')
      | ~ m1_subset_1(C_213,'#skF_2')
      | ~ m1_subset_1(B_212,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_60,c_491])).

tff(c_119,plain,(
    ! [A_101,B_102,C_103] :
      ( k12_lattice3(A_101,B_102,C_103) = k11_lattice3(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v2_lattice3(A_101)
      | ~ v5_orders_2(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    ! [A_64,B_102,C_103] :
      ( k12_lattice3(k2_yellow_1(A_64),B_102,C_103) = k11_lattice3(k2_yellow_1(A_64),B_102,C_103)
      | ~ m1_subset_1(C_103,A_64)
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_131,plain,(
    ! [A_104,B_105,C_106] :
      ( k12_lattice3(k2_yellow_1(A_104),B_105,C_106) = k11_lattice3(k2_yellow_1(A_104),B_105,C_106)
      | ~ m1_subset_1(C_106,A_104)
      | ~ m1_subset_1(B_105,A_104)
      | ~ v2_lattice3(k2_yellow_1(A_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_126])).

tff(c_135,plain,(
    ! [B_107,C_108] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_107,C_108) = k11_lattice3(k2_yellow_1('#skF_2'),B_107,C_108)
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_112,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k12_lattice3(A_95,B_96,C_97),u1_struct_0(A_95))
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v2_lattice3(A_95)
      | ~ v5_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [A_64,B_96,C_97] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_96,C_97),A_64)
      | ~ m1_subset_1(C_97,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_117,plain,(
    ! [A_64,B_96,C_97] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_96,C_97),A_64)
      | ~ m1_subset_1(C_97,A_64)
      | ~ m1_subset_1(B_96,A_64)
      | ~ v2_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_115])).

tff(c_141,plain,(
    ! [B_107,C_108] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_107,C_108),'#skF_2')
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_117])).

tff(c_150,plain,(
    ! [B_107,C_108] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_107,C_108),'#skF_2')
      | ~ m1_subset_1(C_108,'#skF_2')
      | ~ m1_subset_1(B_107,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_141])).

tff(c_134,plain,(
    ! [B_105,C_106] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_105,C_106) = k11_lattice3(k2_yellow_1('#skF_2'),B_105,C_106)
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_231,plain,(
    ! [A_136,B_137,C_138] :
      ( r1_orders_2(A_136,k12_lattice3(A_136,B_137,C_138),C_138)
      | ~ m1_subset_1(k12_lattice3(A_136,B_137,C_138),u1_struct_0(A_136))
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v2_lattice3(A_136)
      | ~ v5_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_243,plain,(
    ! [A_139,B_140,C_141] :
      ( r1_orders_2(A_139,k12_lattice3(A_139,B_140,C_141),C_141)
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v2_lattice3(A_139)
      | ~ v5_orders_2(A_139) ) ),
    inference(resolution,[status(thm)],[c_10,c_231])).

tff(c_250,plain,(
    ! [B_105,C_106] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_105,C_106),C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_243])).

tff(c_256,plain,(
    ! [B_142,C_143] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),C_143)
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
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
    ! [B_142,C_143] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),C_143)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_256,c_171])).

tff(c_262,plain,(
    ! [B_142,C_143] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),C_143)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
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
      ( r1_orders_2(A_126,k12_lattice3(A_126,B_127,C_128),B_127)
      | ~ m1_subset_1(k12_lattice3(A_126,B_127,C_128),u1_struct_0(A_126))
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v2_lattice3(A_126)
      | ~ v5_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_201,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_orders_2(A_129,k12_lattice3(A_129,B_130,C_131),B_130)
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v2_lattice3(A_129)
      | ~ v5_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_208,plain,(
    ! [B_105,C_106] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_105,C_106),B_105)
      | ~ m1_subset_1(C_106,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_106,'#skF_2')
      | ~ m1_subset_1(B_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_201])).

tff(c_214,plain,(
    ! [B_132,C_133] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),B_132)
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_208])).

tff(c_217,plain,(
    ! [B_132,C_133] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),B_132)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_214,c_171])).

tff(c_220,plain,(
    ! [B_132,C_133] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),B_132)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_217])).

tff(c_285,plain,(
    ! [B_148,C_149] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_148,C_149),B_148)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_148,C_149),'#skF_2')
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_220])).

tff(c_100,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(A_86,k3_xboole_0(B_87,C_88))
      | ~ r1_tarski(A_86,C_88)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_104,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_52])).

tff(c_106,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_288,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_106])).

tff(c_291,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_288])).

tff(c_294,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_150,c_291])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_294])).

tff(c_299,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_498,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_495,c_299])).

tff(c_501,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:41:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.46  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.11/1.46  
% 3.11/1.46  %Foreground sorts:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Background operators:
% 3.11/1.46  
% 3.11/1.46  
% 3.11/1.46  %Foreground operators:
% 3.11/1.46  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.11/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.46  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.11/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.11/1.46  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.11/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.46  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.11/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.11/1.46  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.11/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.11/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.11/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.46  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.11/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.11/1.46  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.11/1.46  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.11/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.11/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.11/1.46  
% 3.11/1.48  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.11/1.48  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.11/1.48  tff(f_114, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.11/1.48  tff(f_106, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.11/1.48  tff(f_72, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.11/1.48  tff(f_60, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 3.11/1.48  tff(f_102, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.11/1.48  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.11/1.48  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.11/1.48  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.11/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.11/1.48  tff(c_44, plain, (![A_64]: (u1_struct_0(k2_yellow_1(A_64))=A_64)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.11/1.48  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.48  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 3.11/1.48  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.48  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 3.11/1.48  tff(c_58, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.48  tff(c_38, plain, (![A_62]: (v5_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.48  tff(c_30, plain, (![A_61]: (l1_orders_2(k2_yellow_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.11/1.48  tff(c_320, plain, (![A_165, B_166, C_167]: (k12_lattice3(A_165, B_166, C_167)=k11_lattice3(A_165, B_166, C_167) | ~m1_subset_1(C_167, u1_struct_0(A_165)) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~v2_lattice3(A_165) | ~v5_orders_2(A_165))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.48  tff(c_327, plain, (![A_64, B_166, C_167]: (k12_lattice3(k2_yellow_1(A_64), B_166, C_167)=k11_lattice3(k2_yellow_1(A_64), B_166, C_167) | ~m1_subset_1(C_167, A_64) | ~m1_subset_1(B_166, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_320])).
% 3.11/1.48  tff(c_332, plain, (![A_168, B_169, C_170]: (k12_lattice3(k2_yellow_1(A_168), B_169, C_170)=k11_lattice3(k2_yellow_1(A_168), B_169, C_170) | ~m1_subset_1(C_170, A_168) | ~m1_subset_1(B_169, A_168) | ~v2_lattice3(k2_yellow_1(A_168)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_327])).
% 3.11/1.48  tff(c_336, plain, (![B_171, C_172]: (k12_lattice3(k2_yellow_1('#skF_2'), B_171, C_172)=k11_lattice3(k2_yellow_1('#skF_2'), B_171, C_172) | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_332])).
% 3.11/1.48  tff(c_306, plain, (![A_153, B_154, C_155]: (m1_subset_1(k12_lattice3(A_153, B_154, C_155), u1_struct_0(A_153)) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v2_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.48  tff(c_309, plain, (![A_64, B_154, C_155]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_154, C_155), A_64) | ~m1_subset_1(C_155, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_154, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_306])).
% 3.11/1.48  tff(c_311, plain, (![A_64, B_154, C_155]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_154, C_155), A_64) | ~m1_subset_1(C_155, A_64) | ~m1_subset_1(B_154, A_64) | ~v2_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_309])).
% 3.11/1.48  tff(c_342, plain, (![B_171, C_172]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_171, C_172), '#skF_2') | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_311])).
% 3.11/1.48  tff(c_351, plain, (![B_171, C_172]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_171, C_172), '#skF_2') | ~m1_subset_1(C_172, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_342])).
% 3.11/1.48  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.48  tff(c_335, plain, (![B_169, C_170]: (k12_lattice3(k2_yellow_1('#skF_2'), B_169, C_170)=k11_lattice3(k2_yellow_1('#skF_2'), B_169, C_170) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_332])).
% 3.11/1.48  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k12_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v2_lattice3(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.48  tff(c_378, plain, (![A_181, B_182, C_183]: (r1_orders_2(A_181, k12_lattice3(A_181, B_182, C_183), B_182) | ~m1_subset_1(k12_lattice3(A_181, B_182, C_183), u1_struct_0(A_181)) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v2_lattice3(A_181) | ~v5_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.48  tff(c_395, plain, (![A_187, B_188, C_189]: (r1_orders_2(A_187, k12_lattice3(A_187, B_188, C_189), B_188) | ~m1_subset_1(C_189, u1_struct_0(A_187)) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l1_orders_2(A_187) | ~v2_lattice3(A_187) | ~v5_orders_2(A_187))), inference(resolution, [status(thm)], [c_10, c_378])).
% 3.11/1.48  tff(c_402, plain, (![B_169, C_170]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_169, C_170), B_169) | ~m1_subset_1(C_170, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_395])).
% 3.11/1.48  tff(c_408, plain, (![B_190, C_191]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), B_190) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_402])).
% 3.11/1.48  tff(c_34, plain, (![A_62]: (v3_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.11/1.48  tff(c_355, plain, (![A_173, B_174, C_175]: (r3_orders_2(A_173, B_174, C_175) | ~r1_orders_2(A_173, B_174, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v3_orders_2(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.48  tff(c_362, plain, (![A_64, B_174, C_175]: (r3_orders_2(k2_yellow_1(A_64), B_174, C_175) | ~r1_orders_2(k2_yellow_1(A_64), B_174, C_175) | ~m1_subset_1(C_175, A_64) | ~m1_subset_1(B_174, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_355])).
% 3.11/1.48  tff(c_368, plain, (![A_178, B_179, C_180]: (r3_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~r1_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~m1_subset_1(C_180, A_178) | ~m1_subset_1(B_179, A_178) | v2_struct_0(k2_yellow_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_362])).
% 3.11/1.48  tff(c_50, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_69, u1_struct_0(k2_yellow_1(A_65))) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.11/1.48  tff(c_63, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, A_65) | ~m1_subset_1(B_69, A_65) | v1_xboole_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 3.11/1.48  tff(c_377, plain, (![B_179, C_180, A_178]: (r1_tarski(B_179, C_180) | v1_xboole_0(A_178) | ~r1_orders_2(k2_yellow_1(A_178), B_179, C_180) | ~m1_subset_1(C_180, A_178) | ~m1_subset_1(B_179, A_178) | v2_struct_0(k2_yellow_1(A_178)))), inference(resolution, [status(thm)], [c_368, c_63])).
% 3.11/1.48  tff(c_411, plain, (![B_190, C_191]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), B_190) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(resolution, [status(thm)], [c_408, c_377])).
% 3.11/1.48  tff(c_414, plain, (![B_190, C_191]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), B_190) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_190, C_191), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_191, '#skF_2') | ~m1_subset_1(B_190, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_411])).
% 3.11/1.48  tff(c_425, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_414])).
% 3.11/1.48  tff(c_42, plain, (![A_63]: (~v2_struct_0(k2_yellow_1(A_63)) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.11/1.48  tff(c_440, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_425, c_42])).
% 3.11/1.48  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_440])).
% 3.11/1.48  tff(c_446, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_414])).
% 3.11/1.48  tff(c_463, plain, (![A_204, B_205, C_206]: (r1_orders_2(A_204, k12_lattice3(A_204, B_205, C_206), C_206) | ~m1_subset_1(k12_lattice3(A_204, B_205, C_206), u1_struct_0(A_204)) | ~m1_subset_1(C_206, u1_struct_0(A_204)) | ~m1_subset_1(B_205, u1_struct_0(A_204)) | ~l1_orders_2(A_204) | ~v2_lattice3(A_204) | ~v5_orders_2(A_204))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.48  tff(c_475, plain, (![A_207, B_208, C_209]: (r1_orders_2(A_207, k12_lattice3(A_207, B_208, C_209), C_209) | ~m1_subset_1(C_209, u1_struct_0(A_207)) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l1_orders_2(A_207) | ~v2_lattice3(A_207) | ~v5_orders_2(A_207))), inference(resolution, [status(thm)], [c_10, c_463])).
% 3.11/1.48  tff(c_482, plain, (![B_169, C_170]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_169, C_170), C_170) | ~m1_subset_1(C_170, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_335, c_475])).
% 3.11/1.48  tff(c_488, plain, (![B_210, C_211]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_210, C_211), C_211) | ~m1_subset_1(C_211, '#skF_2') | ~m1_subset_1(B_210, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_482])).
% 3.11/1.48  tff(c_491, plain, (![B_210, C_211]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_210, C_211), C_211) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_210, C_211), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_211, '#skF_2') | ~m1_subset_1(B_210, '#skF_2'))), inference(resolution, [status(thm)], [c_488, c_377])).
% 3.11/1.48  tff(c_495, plain, (![B_212, C_213]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_212, C_213), C_213) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_212, C_213), '#skF_2') | ~m1_subset_1(C_213, '#skF_2') | ~m1_subset_1(B_212, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_446, c_60, c_491])).
% 3.11/1.48  tff(c_119, plain, (![A_101, B_102, C_103]: (k12_lattice3(A_101, B_102, C_103)=k11_lattice3(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v2_lattice3(A_101) | ~v5_orders_2(A_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.11/1.48  tff(c_126, plain, (![A_64, B_102, C_103]: (k12_lattice3(k2_yellow_1(A_64), B_102, C_103)=k11_lattice3(k2_yellow_1(A_64), B_102, C_103) | ~m1_subset_1(C_103, A_64) | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_119])).
% 3.11/1.48  tff(c_131, plain, (![A_104, B_105, C_106]: (k12_lattice3(k2_yellow_1(A_104), B_105, C_106)=k11_lattice3(k2_yellow_1(A_104), B_105, C_106) | ~m1_subset_1(C_106, A_104) | ~m1_subset_1(B_105, A_104) | ~v2_lattice3(k2_yellow_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_126])).
% 3.11/1.48  tff(c_135, plain, (![B_107, C_108]: (k12_lattice3(k2_yellow_1('#skF_2'), B_107, C_108)=k11_lattice3(k2_yellow_1('#skF_2'), B_107, C_108) | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 3.11/1.48  tff(c_112, plain, (![A_95, B_96, C_97]: (m1_subset_1(k12_lattice3(A_95, B_96, C_97), u1_struct_0(A_95)) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v2_lattice3(A_95) | ~v5_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.48  tff(c_115, plain, (![A_64, B_96, C_97]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_96, C_97), A_64) | ~m1_subset_1(C_97, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_112])).
% 3.11/1.49  tff(c_117, plain, (![A_64, B_96, C_97]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_96, C_97), A_64) | ~m1_subset_1(C_97, A_64) | ~m1_subset_1(B_96, A_64) | ~v2_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_115])).
% 3.11/1.49  tff(c_141, plain, (![B_107, C_108]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_107, C_108), '#skF_2') | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_117])).
% 3.11/1.49  tff(c_150, plain, (![B_107, C_108]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_107, C_108), '#skF_2') | ~m1_subset_1(C_108, '#skF_2') | ~m1_subset_1(B_107, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_141])).
% 3.11/1.49  tff(c_134, plain, (![B_105, C_106]: (k12_lattice3(k2_yellow_1('#skF_2'), B_105, C_106)=k11_lattice3(k2_yellow_1('#skF_2'), B_105, C_106) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 3.11/1.49  tff(c_231, plain, (![A_136, B_137, C_138]: (r1_orders_2(A_136, k12_lattice3(A_136, B_137, C_138), C_138) | ~m1_subset_1(k12_lattice3(A_136, B_137, C_138), u1_struct_0(A_136)) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v2_lattice3(A_136) | ~v5_orders_2(A_136))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.49  tff(c_243, plain, (![A_139, B_140, C_141]: (r1_orders_2(A_139, k12_lattice3(A_139, B_140, C_141), C_141) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v2_lattice3(A_139) | ~v5_orders_2(A_139))), inference(resolution, [status(thm)], [c_10, c_231])).
% 3.11/1.49  tff(c_250, plain, (![B_105, C_106]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_105, C_106), C_106) | ~m1_subset_1(C_106, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_243])).
% 3.11/1.49  tff(c_256, plain, (![B_142, C_143]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), C_143) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_250])).
% 3.11/1.49  tff(c_155, plain, (![A_111, B_112, C_113]: (r3_orders_2(A_111, B_112, C_113) | ~r1_orders_2(A_111, B_112, C_113) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.11/1.49  tff(c_162, plain, (![A_64, B_112, C_113]: (r3_orders_2(k2_yellow_1(A_64), B_112, C_113) | ~r1_orders_2(k2_yellow_1(A_64), B_112, C_113) | ~m1_subset_1(C_113, A_64) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_155])).
% 3.11/1.49  tff(c_167, plain, (![A_114, B_115, C_116]: (r3_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~r1_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~m1_subset_1(C_116, A_114) | ~m1_subset_1(B_115, A_114) | v2_struct_0(k2_yellow_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_162])).
% 3.11/1.49  tff(c_171, plain, (![B_115, C_116, A_114]: (r1_tarski(B_115, C_116) | v1_xboole_0(A_114) | ~r1_orders_2(k2_yellow_1(A_114), B_115, C_116) | ~m1_subset_1(C_116, A_114) | ~m1_subset_1(B_115, A_114) | v2_struct_0(k2_yellow_1(A_114)))), inference(resolution, [status(thm)], [c_167, c_63])).
% 3.11/1.49  tff(c_259, plain, (![B_142, C_143]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), C_143) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(resolution, [status(thm)], [c_256, c_171])).
% 3.11/1.49  tff(c_262, plain, (![B_142, C_143]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), C_143) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_259])).
% 3.11/1.49  tff(c_273, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_262])).
% 3.11/1.49  tff(c_276, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_273, c_42])).
% 3.11/1.49  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_276])).
% 3.11/1.49  tff(c_282, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_262])).
% 3.11/1.49  tff(c_189, plain, (![A_126, B_127, C_128]: (r1_orders_2(A_126, k12_lattice3(A_126, B_127, C_128), B_127) | ~m1_subset_1(k12_lattice3(A_126, B_127, C_128), u1_struct_0(A_126)) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v2_lattice3(A_126) | ~v5_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.11/1.49  tff(c_201, plain, (![A_129, B_130, C_131]: (r1_orders_2(A_129, k12_lattice3(A_129, B_130, C_131), B_130) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v2_lattice3(A_129) | ~v5_orders_2(A_129))), inference(resolution, [status(thm)], [c_10, c_189])).
% 3.11/1.49  tff(c_208, plain, (![B_105, C_106]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_105, C_106), B_105) | ~m1_subset_1(C_106, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_106, '#skF_2') | ~m1_subset_1(B_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_201])).
% 3.11/1.49  tff(c_214, plain, (![B_132, C_133]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), B_132) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_208])).
% 3.11/1.49  tff(c_217, plain, (![B_132, C_133]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), B_132) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(resolution, [status(thm)], [c_214, c_171])).
% 3.11/1.49  tff(c_220, plain, (![B_132, C_133]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), B_132) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_217])).
% 3.11/1.49  tff(c_285, plain, (![B_148, C_149]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_148, C_149), B_148) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_148, C_149), '#skF_2') | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_282, c_220])).
% 3.11/1.49  tff(c_100, plain, (![A_86, B_87, C_88]: (r1_tarski(A_86, k3_xboole_0(B_87, C_88)) | ~r1_tarski(A_86, C_88) | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.49  tff(c_52, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.11/1.49  tff(c_104, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_100, c_52])).
% 3.11/1.49  tff(c_106, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_104])).
% 3.11/1.49  tff(c_288, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_285, c_106])).
% 3.11/1.49  tff(c_291, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_288])).
% 3.11/1.49  tff(c_294, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_150, c_291])).
% 3.11/1.49  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_294])).
% 3.11/1.49  tff(c_299, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_104])).
% 3.11/1.49  tff(c_498, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_495, c_299])).
% 3.11/1.49  tff(c_501, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_498])).
% 3.11/1.49  tff(c_516, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_351, c_501])).
% 3.11/1.49  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_516])).
% 3.11/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.49  
% 3.11/1.49  Inference rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Ref     : 0
% 3.11/1.49  #Sup     : 86
% 3.11/1.49  #Fact    : 0
% 3.11/1.49  #Define  : 0
% 3.11/1.49  #Split   : 3
% 3.11/1.49  #Chain   : 0
% 3.11/1.49  #Close   : 0
% 3.11/1.49  
% 3.11/1.49  Ordering : KBO
% 3.11/1.49  
% 3.11/1.49  Simplification rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Subsume      : 11
% 3.11/1.49  #Demod        : 158
% 3.11/1.49  #Tautology    : 18
% 3.11/1.49  #SimpNegUnit  : 11
% 3.11/1.49  #BackRed      : 0
% 3.11/1.49  
% 3.11/1.49  #Partial instantiations: 0
% 3.11/1.49  #Strategies tried      : 1
% 3.11/1.49  
% 3.11/1.49  Timing (in seconds)
% 3.11/1.49  ----------------------
% 3.11/1.49  Preprocessing        : 0.36
% 3.11/1.49  Parsing              : 0.18
% 3.11/1.49  CNF conversion       : 0.03
% 3.11/1.49  Main loop            : 0.33
% 3.11/1.49  Inferencing          : 0.13
% 3.11/1.49  Reduction            : 0.11
% 3.11/1.49  Demodulation         : 0.08
% 3.11/1.49  BG Simplification    : 0.02
% 3.11/1.49  Subsumption          : 0.06
% 3.11/1.49  Abstraction          : 0.02
% 3.11/1.49  MUC search           : 0.00
% 3.11/1.49  Cooper               : 0.00
% 3.11/1.49  Total                : 0.74
% 3.11/1.49  Index Insertion      : 0.00
% 3.11/1.49  Index Deletion       : 0.00
% 3.11/1.49  Index Matching       : 0.00
% 3.11/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
