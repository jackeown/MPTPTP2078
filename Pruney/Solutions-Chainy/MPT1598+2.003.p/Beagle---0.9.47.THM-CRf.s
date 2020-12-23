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
% DateTime   : Thu Dec  3 10:25:21 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 833 expanded)
%              Number of leaves         :   38 ( 336 expanded)
%              Depth                    :   14
%              Number of atoms          :  410 (2455 expanded)
%              Number of equality atoms :   23 ( 462 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_148,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_110,axiom,(
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
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

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

tff(f_161,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_46,plain,(
    ! [A_70] : u1_struct_0(k2_yellow_1(A_70)) = A_70 ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_63,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_60,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_40,plain,(
    ! [A_68] : v5_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    ! [A_67] : l1_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_498,plain,(
    ! [A_177,B_178,C_179] :
      ( k13_lattice3(A_177,B_178,C_179) = k10_lattice3(A_177,B_178,C_179)
      | ~ m1_subset_1(C_179,u1_struct_0(A_177))
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177)
      | ~ v1_lattice3(A_177)
      | ~ v5_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_505,plain,(
    ! [A_70,B_178,C_179] :
      ( k13_lattice3(k2_yellow_1(A_70),B_178,C_179) = k10_lattice3(k2_yellow_1(A_70),B_178,C_179)
      | ~ m1_subset_1(C_179,A_70)
      | ~ m1_subset_1(B_178,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_498])).

tff(c_510,plain,(
    ! [A_180,B_181,C_182] :
      ( k13_lattice3(k2_yellow_1(A_180),B_181,C_182) = k10_lattice3(k2_yellow_1(A_180),B_181,C_182)
      | ~ m1_subset_1(C_182,A_180)
      | ~ m1_subset_1(B_181,A_180)
      | ~ v1_lattice3(k2_yellow_1(A_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_505])).

tff(c_514,plain,(
    ! [B_183,C_184] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_183,C_184) = k10_lattice3(k2_yellow_1('#skF_2'),B_183,C_184)
      | ~ m1_subset_1(C_184,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_510])).

tff(c_387,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1(k13_lattice3(A_154,B_155,C_156),u1_struct_0(A_154))
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154)
      | ~ v1_lattice3(A_154)
      | ~ v5_orders_2(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_390,plain,(
    ! [A_70,B_155,C_156] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_70),B_155,C_156),A_70)
      | ~ m1_subset_1(C_156,u1_struct_0(k2_yellow_1(A_70)))
      | ~ m1_subset_1(B_155,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_387])).

tff(c_392,plain,(
    ! [A_70,B_155,C_156] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_70),B_155,C_156),A_70)
      | ~ m1_subset_1(C_156,A_70)
      | ~ m1_subset_1(B_155,A_70)
      | ~ v1_lattice3(k2_yellow_1(A_70)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_390])).

tff(c_520,plain,(
    ! [B_183,C_184] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_183,C_184),'#skF_2')
      | ~ m1_subset_1(C_184,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_184,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_392])).

tff(c_529,plain,(
    ! [B_183,C_184] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_183,C_184),'#skF_2')
      | ~ m1_subset_1(C_184,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_520])).

tff(c_393,plain,(
    ! [A_157,C_158,B_159] :
      ( k10_lattice3(A_157,C_158,B_159) = k10_lattice3(A_157,B_159,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0(A_157))
      | ~ m1_subset_1(B_159,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v1_lattice3(A_157)
      | ~ v5_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_397,plain,(
    ! [A_70,C_158,B_159] :
      ( k10_lattice3(k2_yellow_1(A_70),C_158,B_159) = k10_lattice3(k2_yellow_1(A_70),B_159,C_158)
      | ~ m1_subset_1(C_158,A_70)
      | ~ m1_subset_1(B_159,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_393])).

tff(c_406,plain,(
    ! [A_163,C_164,B_165] :
      ( k10_lattice3(k2_yellow_1(A_163),C_164,B_165) = k10_lattice3(k2_yellow_1(A_163),B_165,C_164)
      | ~ m1_subset_1(C_164,A_163)
      | ~ m1_subset_1(B_165,A_163)
      | ~ v1_lattice3(k2_yellow_1(A_163)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_397])).

tff(c_409,plain,(
    ! [C_164,B_165] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_164,B_165) = k10_lattice3(k2_yellow_1('#skF_2'),B_165,C_164)
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_165,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_406])).

tff(c_551,plain,(
    ! [A_190,C_191,B_192] :
      ( r1_orders_2(A_190,C_191,k10_lattice3(A_190,B_192,C_191))
      | ~ m1_subset_1(k10_lattice3(A_190,B_192,C_191),u1_struct_0(A_190))
      | ~ m1_subset_1(C_191,u1_struct_0(A_190))
      | ~ m1_subset_1(B_192,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v1_lattice3(A_190)
      | ~ v5_orders_2(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_553,plain,(
    ! [C_164,B_165] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_164,k10_lattice3(k2_yellow_1('#skF_2'),B_165,C_164))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_164,B_165),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_164,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_165,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_551])).

tff(c_559,plain,(
    ! [C_164,B_165] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_164,k10_lattice3(k2_yellow_1('#skF_2'),B_165,C_164))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_164,B_165),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_165,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_553])).

tff(c_569,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_559])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_572,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_569,c_8])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60,c_572])).

tff(c_581,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_559])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_555,plain,(
    ! [B_165,C_164] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_165,k10_lattice3(k2_yellow_1('#skF_2'),C_164,B_165))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_165,C_164),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_164,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_165,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_551])).

tff(c_561,plain,(
    ! [B_165,C_164] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_165,k10_lattice3(k2_yellow_1('#skF_2'),C_164,B_165))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_165,C_164),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_164,'#skF_2')
      | ~ m1_subset_1(B_165,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_555])).

tff(c_582,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_582])).

tff(c_586,plain,(
    ! [B_196,C_197] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_196,k10_lattice3(k2_yellow_1('#skF_2'),C_197,B_196))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_196,C_197),'#skF_2')
      | ~ m1_subset_1(C_197,'#skF_2')
      | ~ m1_subset_1(B_196,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_36,plain,(
    ! [A_68] : v3_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_478,plain,(
    ! [A_168,B_169,C_170] :
      ( r3_orders_2(A_168,B_169,C_170)
      | ~ r1_orders_2(A_168,B_169,C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(A_168))
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ l1_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_485,plain,(
    ! [A_70,B_169,C_170] :
      ( r3_orders_2(k2_yellow_1(A_70),B_169,C_170)
      | ~ r1_orders_2(k2_yellow_1(A_70),B_169,C_170)
      | ~ m1_subset_1(C_170,A_70)
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v3_orders_2(k2_yellow_1(A_70))
      | v2_struct_0(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_478])).

tff(c_492,plain,(
    ! [A_171,B_172,C_173] :
      ( r3_orders_2(k2_yellow_1(A_171),B_172,C_173)
      | ~ r1_orders_2(k2_yellow_1(A_171),B_172,C_173)
      | ~ m1_subset_1(C_173,A_171)
      | ~ m1_subset_1(B_172,A_171)
      | v2_struct_0(k2_yellow_1(A_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_485])).

tff(c_52,plain,(
    ! [B_75,C_77,A_71] :
      ( r1_tarski(B_75,C_77)
      | ~ r3_orders_2(k2_yellow_1(A_71),B_75,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(k2_yellow_1(A_71)))
      | ~ m1_subset_1(B_75,u1_struct_0(k2_yellow_1(A_71)))
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_65,plain,(
    ! [B_75,C_77,A_71] :
      ( r1_tarski(B_75,C_77)
      | ~ r3_orders_2(k2_yellow_1(A_71),B_75,C_77)
      | ~ m1_subset_1(C_77,A_71)
      | ~ m1_subset_1(B_75,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_52])).

tff(c_496,plain,(
    ! [B_172,C_173,A_171] :
      ( r1_tarski(B_172,C_173)
      | v1_xboole_0(A_171)
      | ~ r1_orders_2(k2_yellow_1(A_171),B_172,C_173)
      | ~ m1_subset_1(C_173,A_171)
      | ~ m1_subset_1(B_172,A_171)
      | v2_struct_0(k2_yellow_1(A_171)) ) ),
    inference(resolution,[status(thm)],[c_492,c_65])).

tff(c_589,plain,(
    ! [B_196,C_197] :
      ( r1_tarski(B_196,k10_lattice3(k2_yellow_1('#skF_2'),C_197,B_196))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_197,B_196),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_196,C_197),'#skF_2')
      | ~ m1_subset_1(C_197,'#skF_2')
      | ~ m1_subset_1(B_196,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_586,c_496])).

tff(c_627,plain,(
    ! [B_203,C_204] :
      ( r1_tarski(B_203,k10_lattice3(k2_yellow_1('#skF_2'),C_204,B_203))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_204,B_203),'#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_203,C_204),'#skF_2')
      | ~ m1_subset_1(C_204,'#skF_2')
      | ~ m1_subset_1(B_203,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_62,c_589])).

tff(c_113,plain,(
    ! [A_106,B_107,C_108] :
      ( k13_lattice3(A_106,B_107,C_108) = k10_lattice3(A_106,B_107,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v1_lattice3(A_106)
      | ~ v5_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_120,plain,(
    ! [A_70,B_107,C_108] :
      ( k13_lattice3(k2_yellow_1(A_70),B_107,C_108) = k10_lattice3(k2_yellow_1(A_70),B_107,C_108)
      | ~ m1_subset_1(C_108,A_70)
      | ~ m1_subset_1(B_107,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_125,plain,(
    ! [A_109,B_110,C_111] :
      ( k13_lattice3(k2_yellow_1(A_109),B_110,C_111) = k10_lattice3(k2_yellow_1(A_109),B_110,C_111)
      | ~ m1_subset_1(C_111,A_109)
      | ~ m1_subset_1(B_110,A_109)
      | ~ v1_lattice3(k2_yellow_1(A_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_120])).

tff(c_129,plain,(
    ! [B_112,C_113] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_112,C_113) = k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113)
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_106,plain,(
    ! [A_100,B_101,C_102] :
      ( m1_subset_1(k13_lattice3(A_100,B_101,C_102),u1_struct_0(A_100))
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_orders_2(A_100)
      | ~ v1_lattice3(A_100)
      | ~ v5_orders_2(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,(
    ! [A_70,B_101,C_102] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_70),B_101,C_102),A_70)
      | ~ m1_subset_1(C_102,u1_struct_0(k2_yellow_1(A_70)))
      | ~ m1_subset_1(B_101,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_106])).

tff(c_111,plain,(
    ! [A_70,B_101,C_102] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_70),B_101,C_102),A_70)
      | ~ m1_subset_1(C_102,A_70)
      | ~ m1_subset_1(B_101,A_70)
      | ~ v1_lattice3(k2_yellow_1(A_70)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_109])).

tff(c_135,plain,(
    ! [B_112,C_113] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113),'#skF_2')
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_111])).

tff(c_144,plain,(
    ! [B_112,C_113] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113),'#skF_2')
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_135])).

tff(c_156,plain,(
    ! [A_122,C_123,B_124] :
      ( k10_lattice3(A_122,C_123,B_124) = k10_lattice3(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_124,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_163,plain,(
    ! [A_70,C_123,B_124] :
      ( k10_lattice3(k2_yellow_1(A_70),C_123,B_124) = k10_lattice3(k2_yellow_1(A_70),B_124,C_123)
      | ~ m1_subset_1(C_123,A_70)
      | ~ m1_subset_1(B_124,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v1_lattice3(k2_yellow_1(A_70))
      | ~ v5_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_156])).

tff(c_180,plain,(
    ! [A_128,C_129,B_130] :
      ( k10_lattice3(k2_yellow_1(A_128),C_129,B_130) = k10_lattice3(k2_yellow_1(A_128),B_130,C_129)
      | ~ m1_subset_1(C_129,A_128)
      | ~ m1_subset_1(B_130,A_128)
      | ~ v1_lattice3(k2_yellow_1(A_128)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_163])).

tff(c_183,plain,(
    ! [C_129,B_130] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_129,B_130) = k10_lattice3(k2_yellow_1('#skF_2'),B_130,C_129)
      | ~ m1_subset_1(C_129,'#skF_2')
      | ~ m1_subset_1(B_130,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_180])).

tff(c_247,plain,(
    ! [A_133,C_134,B_135] :
      ( r1_orders_2(A_133,C_134,k10_lattice3(A_133,B_135,C_134))
      | ~ m1_subset_1(k10_lattice3(A_133,B_135,C_134),u1_struct_0(A_133))
      | ~ m1_subset_1(C_134,u1_struct_0(A_133))
      | ~ m1_subset_1(B_135,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v1_lattice3(A_133)
      | ~ v5_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_251,plain,(
    ! [B_130,C_129] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_130,k10_lattice3(k2_yellow_1('#skF_2'),C_129,B_130))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_130,C_129),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_130,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_129,'#skF_2')
      | ~ m1_subset_1(B_130,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_247])).

tff(c_257,plain,(
    ! [B_130,C_129] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_130,k10_lattice3(k2_yellow_1('#skF_2'),C_129,B_130))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_130,C_129),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_129,'#skF_2')
      | ~ m1_subset_1(B_130,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_251])).

tff(c_275,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_278,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_275,c_8])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60,c_278])).

tff(c_287,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_288,plain,(
    ! [B_142,C_143] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_142,k10_lattice3(k2_yellow_1('#skF_2'),C_143,B_142))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),'#skF_2')
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_168,plain,(
    ! [A_125,B_126,C_127] :
      ( r3_orders_2(A_125,B_126,C_127)
      | ~ r1_orders_2(A_125,B_126,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_175,plain,(
    ! [A_70,B_126,C_127] :
      ( r3_orders_2(k2_yellow_1(A_70),B_126,C_127)
      | ~ r1_orders_2(k2_yellow_1(A_70),B_126,C_127)
      | ~ m1_subset_1(C_127,A_70)
      | ~ m1_subset_1(B_126,u1_struct_0(k2_yellow_1(A_70)))
      | ~ l1_orders_2(k2_yellow_1(A_70))
      | ~ v3_orders_2(k2_yellow_1(A_70))
      | v2_struct_0(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_168])).

tff(c_260,plain,(
    ! [A_136,B_137,C_138] :
      ( r3_orders_2(k2_yellow_1(A_136),B_137,C_138)
      | ~ r1_orders_2(k2_yellow_1(A_136),B_137,C_138)
      | ~ m1_subset_1(C_138,A_136)
      | ~ m1_subset_1(B_137,A_136)
      | v2_struct_0(k2_yellow_1(A_136)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_175])).

tff(c_269,plain,(
    ! [B_137,C_138,A_136] :
      ( r1_tarski(B_137,C_138)
      | v1_xboole_0(A_136)
      | ~ r1_orders_2(k2_yellow_1(A_136),B_137,C_138)
      | ~ m1_subset_1(C_138,A_136)
      | ~ m1_subset_1(B_137,A_136)
      | v2_struct_0(k2_yellow_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_260,c_65])).

tff(c_291,plain,(
    ! [B_142,C_143] :
      ( r1_tarski(B_142,k10_lattice3(k2_yellow_1('#skF_2'),C_143,B_142))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_143,B_142),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_142,C_143),'#skF_2')
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_288,c_269])).

tff(c_302,plain,(
    ! [B_144,C_145] :
      ( r1_tarski(B_144,k10_lattice3(k2_yellow_1('#skF_2'),C_145,B_144))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_145,B_144),'#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),'#skF_2')
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_62,c_291])).

tff(c_184,plain,(
    ! [C_131,B_132] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_131,B_132) = k10_lattice3(k2_yellow_1('#skF_2'),B_132,C_131)
      | ~ m1_subset_1(C_131,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_180])).

tff(c_94,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(k2_xboole_0(A_91,C_92),B_93)
      | ~ r1_tarski(C_92,B_93)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_98,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_94,c_54])).

tff(c_100,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_205,plain,
    ( ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_100])).

tff(c_232,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_205])).

tff(c_305,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_302,c_232])).

tff(c_314,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_305])).

tff(c_330,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_339,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_330])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_339])).

tff(c_348,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_375,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_348])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_375])).

tff(c_380,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_630,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_627,c_380])).

tff(c_639,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_630])).

tff(c_640,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_643,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_529,c_640])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_643])).

tff(c_648,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_652,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_529,c_648])).

tff(c_662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.49  
% 3.30/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.50  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.30/1.50  
% 3.30/1.50  %Foreground sorts:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Background operators:
% 3.30/1.50  
% 3.30/1.50  
% 3.30/1.50  %Foreground operators:
% 3.30/1.50  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.30/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.50  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.30/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.50  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.30/1.50  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.30/1.50  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.30/1.50  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.30/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.50  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.30/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.30/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.30/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.50  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.30/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.50  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.30/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.30/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.50  
% 3.30/1.53  tff(f_148, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.30/1.53  tff(f_175, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_1)).
% 3.30/1.53  tff(f_136, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.30/1.53  tff(f_128, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.30/1.53  tff(f_110, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.30/1.53  tff(f_65, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 3.30/1.53  tff(f_124, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_lattice3)).
% 3.30/1.53  tff(f_98, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 3.30/1.53  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.30/1.53  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.30/1.53  tff(f_161, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.30/1.53  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.30/1.53  tff(c_46, plain, (![A_70]: (u1_struct_0(k2_yellow_1(A_70))=A_70)), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.30/1.53  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.30/1.53  tff(c_63, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 3.30/1.53  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.30/1.53  tff(c_64, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 3.30/1.53  tff(c_60, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.30/1.53  tff(c_40, plain, (![A_68]: (v5_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.30/1.53  tff(c_32, plain, (![A_67]: (l1_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.30/1.53  tff(c_498, plain, (![A_177, B_178, C_179]: (k13_lattice3(A_177, B_178, C_179)=k10_lattice3(A_177, B_178, C_179) | ~m1_subset_1(C_179, u1_struct_0(A_177)) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~l1_orders_2(A_177) | ~v1_lattice3(A_177) | ~v5_orders_2(A_177))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.30/1.53  tff(c_505, plain, (![A_70, B_178, C_179]: (k13_lattice3(k2_yellow_1(A_70), B_178, C_179)=k10_lattice3(k2_yellow_1(A_70), B_178, C_179) | ~m1_subset_1(C_179, A_70) | ~m1_subset_1(B_178, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_498])).
% 3.30/1.53  tff(c_510, plain, (![A_180, B_181, C_182]: (k13_lattice3(k2_yellow_1(A_180), B_181, C_182)=k10_lattice3(k2_yellow_1(A_180), B_181, C_182) | ~m1_subset_1(C_182, A_180) | ~m1_subset_1(B_181, A_180) | ~v1_lattice3(k2_yellow_1(A_180)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_505])).
% 3.30/1.53  tff(c_514, plain, (![B_183, C_184]: (k13_lattice3(k2_yellow_1('#skF_2'), B_183, C_184)=k10_lattice3(k2_yellow_1('#skF_2'), B_183, C_184) | ~m1_subset_1(C_184, '#skF_2') | ~m1_subset_1(B_183, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_510])).
% 3.30/1.53  tff(c_387, plain, (![A_154, B_155, C_156]: (m1_subset_1(k13_lattice3(A_154, B_155, C_156), u1_struct_0(A_154)) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_orders_2(A_154) | ~v1_lattice3(A_154) | ~v5_orders_2(A_154))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.53  tff(c_390, plain, (![A_70, B_155, C_156]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_70), B_155, C_156), A_70) | ~m1_subset_1(C_156, u1_struct_0(k2_yellow_1(A_70))) | ~m1_subset_1(B_155, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_387])).
% 3.30/1.53  tff(c_392, plain, (![A_70, B_155, C_156]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_70), B_155, C_156), A_70) | ~m1_subset_1(C_156, A_70) | ~m1_subset_1(B_155, A_70) | ~v1_lattice3(k2_yellow_1(A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_390])).
% 3.30/1.53  tff(c_520, plain, (![B_183, C_184]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_183, C_184), '#skF_2') | ~m1_subset_1(C_184, '#skF_2') | ~m1_subset_1(B_183, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_184, '#skF_2') | ~m1_subset_1(B_183, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_514, c_392])).
% 3.30/1.53  tff(c_529, plain, (![B_183, C_184]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_183, C_184), '#skF_2') | ~m1_subset_1(C_184, '#skF_2') | ~m1_subset_1(B_183, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_520])).
% 3.30/1.53  tff(c_393, plain, (![A_157, C_158, B_159]: (k10_lattice3(A_157, C_158, B_159)=k10_lattice3(A_157, B_159, C_158) | ~m1_subset_1(C_158, u1_struct_0(A_157)) | ~m1_subset_1(B_159, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v1_lattice3(A_157) | ~v5_orders_2(A_157))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.30/1.53  tff(c_397, plain, (![A_70, C_158, B_159]: (k10_lattice3(k2_yellow_1(A_70), C_158, B_159)=k10_lattice3(k2_yellow_1(A_70), B_159, C_158) | ~m1_subset_1(C_158, A_70) | ~m1_subset_1(B_159, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_393])).
% 3.30/1.53  tff(c_406, plain, (![A_163, C_164, B_165]: (k10_lattice3(k2_yellow_1(A_163), C_164, B_165)=k10_lattice3(k2_yellow_1(A_163), B_165, C_164) | ~m1_subset_1(C_164, A_163) | ~m1_subset_1(B_165, A_163) | ~v1_lattice3(k2_yellow_1(A_163)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_397])).
% 3.30/1.53  tff(c_409, plain, (![C_164, B_165]: (k10_lattice3(k2_yellow_1('#skF_2'), C_164, B_165)=k10_lattice3(k2_yellow_1('#skF_2'), B_165, C_164) | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_165, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_406])).
% 3.30/1.53  tff(c_551, plain, (![A_190, C_191, B_192]: (r1_orders_2(A_190, C_191, k10_lattice3(A_190, B_192, C_191)) | ~m1_subset_1(k10_lattice3(A_190, B_192, C_191), u1_struct_0(A_190)) | ~m1_subset_1(C_191, u1_struct_0(A_190)) | ~m1_subset_1(B_192, u1_struct_0(A_190)) | ~l1_orders_2(A_190) | ~v1_lattice3(A_190) | ~v5_orders_2(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.30/1.53  tff(c_553, plain, (![C_164, B_165]: (r1_orders_2(k2_yellow_1('#skF_2'), C_164, k10_lattice3(k2_yellow_1('#skF_2'), B_165, C_164)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_164, B_165), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_164, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_165, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_551])).
% 3.30/1.53  tff(c_559, plain, (![C_164, B_165]: (r1_orders_2(k2_yellow_1('#skF_2'), C_164, k10_lattice3(k2_yellow_1('#skF_2'), B_165, C_164)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_164, B_165), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_165, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_553])).
% 3.30/1.53  tff(c_569, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_559])).
% 3.30/1.53  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.53  tff(c_572, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_569, c_8])).
% 3.30/1.53  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_60, c_572])).
% 3.30/1.53  tff(c_581, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_559])).
% 3.30/1.53  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.30/1.53  tff(c_555, plain, (![B_165, C_164]: (r1_orders_2(k2_yellow_1('#skF_2'), B_165, k10_lattice3(k2_yellow_1('#skF_2'), C_164, B_165)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_165, C_164), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_164, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_165, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_551])).
% 3.30/1.53  tff(c_561, plain, (![B_165, C_164]: (r1_orders_2(k2_yellow_1('#skF_2'), B_165, k10_lattice3(k2_yellow_1('#skF_2'), C_164, B_165)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_165, C_164), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_164, '#skF_2') | ~m1_subset_1(B_165, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_555])).
% 3.30/1.53  tff(c_582, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_561])).
% 3.30/1.53  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_582])).
% 3.30/1.53  tff(c_586, plain, (![B_196, C_197]: (r1_orders_2(k2_yellow_1('#skF_2'), B_196, k10_lattice3(k2_yellow_1('#skF_2'), C_197, B_196)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_196, C_197), '#skF_2') | ~m1_subset_1(C_197, '#skF_2') | ~m1_subset_1(B_196, '#skF_2'))), inference(splitRight, [status(thm)], [c_561])).
% 3.30/1.53  tff(c_36, plain, (![A_68]: (v3_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.30/1.53  tff(c_478, plain, (![A_168, B_169, C_170]: (r3_orders_2(A_168, B_169, C_170) | ~r1_orders_2(A_168, B_169, C_170) | ~m1_subset_1(C_170, u1_struct_0(A_168)) | ~m1_subset_1(B_169, u1_struct_0(A_168)) | ~l1_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.53  tff(c_485, plain, (![A_70, B_169, C_170]: (r3_orders_2(k2_yellow_1(A_70), B_169, C_170) | ~r1_orders_2(k2_yellow_1(A_70), B_169, C_170) | ~m1_subset_1(C_170, A_70) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v3_orders_2(k2_yellow_1(A_70)) | v2_struct_0(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_478])).
% 3.30/1.53  tff(c_492, plain, (![A_171, B_172, C_173]: (r3_orders_2(k2_yellow_1(A_171), B_172, C_173) | ~r1_orders_2(k2_yellow_1(A_171), B_172, C_173) | ~m1_subset_1(C_173, A_171) | ~m1_subset_1(B_172, A_171) | v2_struct_0(k2_yellow_1(A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_485])).
% 3.30/1.53  tff(c_52, plain, (![B_75, C_77, A_71]: (r1_tarski(B_75, C_77) | ~r3_orders_2(k2_yellow_1(A_71), B_75, C_77) | ~m1_subset_1(C_77, u1_struct_0(k2_yellow_1(A_71))) | ~m1_subset_1(B_75, u1_struct_0(k2_yellow_1(A_71))) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.30/1.53  tff(c_65, plain, (![B_75, C_77, A_71]: (r1_tarski(B_75, C_77) | ~r3_orders_2(k2_yellow_1(A_71), B_75, C_77) | ~m1_subset_1(C_77, A_71) | ~m1_subset_1(B_75, A_71) | v1_xboole_0(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_52])).
% 3.30/1.53  tff(c_496, plain, (![B_172, C_173, A_171]: (r1_tarski(B_172, C_173) | v1_xboole_0(A_171) | ~r1_orders_2(k2_yellow_1(A_171), B_172, C_173) | ~m1_subset_1(C_173, A_171) | ~m1_subset_1(B_172, A_171) | v2_struct_0(k2_yellow_1(A_171)))), inference(resolution, [status(thm)], [c_492, c_65])).
% 3.30/1.53  tff(c_589, plain, (![B_196, C_197]: (r1_tarski(B_196, k10_lattice3(k2_yellow_1('#skF_2'), C_197, B_196)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_197, B_196), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_196, C_197), '#skF_2') | ~m1_subset_1(C_197, '#skF_2') | ~m1_subset_1(B_196, '#skF_2'))), inference(resolution, [status(thm)], [c_586, c_496])).
% 3.30/1.53  tff(c_627, plain, (![B_203, C_204]: (r1_tarski(B_203, k10_lattice3(k2_yellow_1('#skF_2'), C_204, B_203)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_204, B_203), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_203, C_204), '#skF_2') | ~m1_subset_1(C_204, '#skF_2') | ~m1_subset_1(B_203, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_581, c_62, c_589])).
% 3.30/1.53  tff(c_113, plain, (![A_106, B_107, C_108]: (k13_lattice3(A_106, B_107, C_108)=k10_lattice3(A_106, B_107, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v1_lattice3(A_106) | ~v5_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.30/1.53  tff(c_120, plain, (![A_70, B_107, C_108]: (k13_lattice3(k2_yellow_1(A_70), B_107, C_108)=k10_lattice3(k2_yellow_1(A_70), B_107, C_108) | ~m1_subset_1(C_108, A_70) | ~m1_subset_1(B_107, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_113])).
% 3.30/1.53  tff(c_125, plain, (![A_109, B_110, C_111]: (k13_lattice3(k2_yellow_1(A_109), B_110, C_111)=k10_lattice3(k2_yellow_1(A_109), B_110, C_111) | ~m1_subset_1(C_111, A_109) | ~m1_subset_1(B_110, A_109) | ~v1_lattice3(k2_yellow_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_120])).
% 3.30/1.53  tff(c_129, plain, (![B_112, C_113]: (k13_lattice3(k2_yellow_1('#skF_2'), B_112, C_113)=k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113) | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_125])).
% 3.30/1.53  tff(c_106, plain, (![A_100, B_101, C_102]: (m1_subset_1(k13_lattice3(A_100, B_101, C_102), u1_struct_0(A_100)) | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_orders_2(A_100) | ~v1_lattice3(A_100) | ~v5_orders_2(A_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.53  tff(c_109, plain, (![A_70, B_101, C_102]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_70), B_101, C_102), A_70) | ~m1_subset_1(C_102, u1_struct_0(k2_yellow_1(A_70))) | ~m1_subset_1(B_101, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_106])).
% 3.30/1.53  tff(c_111, plain, (![A_70, B_101, C_102]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_70), B_101, C_102), A_70) | ~m1_subset_1(C_102, A_70) | ~m1_subset_1(B_101, A_70) | ~v1_lattice3(k2_yellow_1(A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_109])).
% 3.30/1.53  tff(c_135, plain, (![B_112, C_113]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113), '#skF_2') | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_111])).
% 3.30/1.53  tff(c_144, plain, (![B_112, C_113]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113), '#skF_2') | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_135])).
% 3.30/1.53  tff(c_156, plain, (![A_122, C_123, B_124]: (k10_lattice3(A_122, C_123, B_124)=k10_lattice3(A_122, B_124, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_124, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v1_lattice3(A_122) | ~v5_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.30/1.53  tff(c_163, plain, (![A_70, C_123, B_124]: (k10_lattice3(k2_yellow_1(A_70), C_123, B_124)=k10_lattice3(k2_yellow_1(A_70), B_124, C_123) | ~m1_subset_1(C_123, A_70) | ~m1_subset_1(B_124, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v1_lattice3(k2_yellow_1(A_70)) | ~v5_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_156])).
% 3.30/1.53  tff(c_180, plain, (![A_128, C_129, B_130]: (k10_lattice3(k2_yellow_1(A_128), C_129, B_130)=k10_lattice3(k2_yellow_1(A_128), B_130, C_129) | ~m1_subset_1(C_129, A_128) | ~m1_subset_1(B_130, A_128) | ~v1_lattice3(k2_yellow_1(A_128)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_163])).
% 3.30/1.53  tff(c_183, plain, (![C_129, B_130]: (k10_lattice3(k2_yellow_1('#skF_2'), C_129, B_130)=k10_lattice3(k2_yellow_1('#skF_2'), B_130, C_129) | ~m1_subset_1(C_129, '#skF_2') | ~m1_subset_1(B_130, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_180])).
% 3.30/1.53  tff(c_247, plain, (![A_133, C_134, B_135]: (r1_orders_2(A_133, C_134, k10_lattice3(A_133, B_135, C_134)) | ~m1_subset_1(k10_lattice3(A_133, B_135, C_134), u1_struct_0(A_133)) | ~m1_subset_1(C_134, u1_struct_0(A_133)) | ~m1_subset_1(B_135, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v1_lattice3(A_133) | ~v5_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.30/1.53  tff(c_251, plain, (![B_130, C_129]: (r1_orders_2(k2_yellow_1('#skF_2'), B_130, k10_lattice3(k2_yellow_1('#skF_2'), C_129, B_130)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_130, C_129), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_130, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_129, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_129, '#skF_2') | ~m1_subset_1(B_130, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_247])).
% 3.30/1.53  tff(c_257, plain, (![B_130, C_129]: (r1_orders_2(k2_yellow_1('#skF_2'), B_130, k10_lattice3(k2_yellow_1('#skF_2'), C_129, B_130)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_130, C_129), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_129, '#skF_2') | ~m1_subset_1(B_130, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_251])).
% 3.30/1.53  tff(c_275, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_257])).
% 3.30/1.53  tff(c_278, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_275, c_8])).
% 3.30/1.53  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_60, c_278])).
% 3.30/1.53  tff(c_287, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_257])).
% 3.30/1.53  tff(c_288, plain, (![B_142, C_143]: (r1_orders_2(k2_yellow_1('#skF_2'), B_142, k10_lattice3(k2_yellow_1('#skF_2'), C_143, B_142)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), '#skF_2') | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(splitRight, [status(thm)], [c_257])).
% 3.30/1.53  tff(c_168, plain, (![A_125, B_126, C_127]: (r3_orders_2(A_125, B_126, C_127) | ~r1_orders_2(A_125, B_126, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.53  tff(c_175, plain, (![A_70, B_126, C_127]: (r3_orders_2(k2_yellow_1(A_70), B_126, C_127) | ~r1_orders_2(k2_yellow_1(A_70), B_126, C_127) | ~m1_subset_1(C_127, A_70) | ~m1_subset_1(B_126, u1_struct_0(k2_yellow_1(A_70))) | ~l1_orders_2(k2_yellow_1(A_70)) | ~v3_orders_2(k2_yellow_1(A_70)) | v2_struct_0(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_168])).
% 3.30/1.53  tff(c_260, plain, (![A_136, B_137, C_138]: (r3_orders_2(k2_yellow_1(A_136), B_137, C_138) | ~r1_orders_2(k2_yellow_1(A_136), B_137, C_138) | ~m1_subset_1(C_138, A_136) | ~m1_subset_1(B_137, A_136) | v2_struct_0(k2_yellow_1(A_136)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_175])).
% 3.30/1.53  tff(c_269, plain, (![B_137, C_138, A_136]: (r1_tarski(B_137, C_138) | v1_xboole_0(A_136) | ~r1_orders_2(k2_yellow_1(A_136), B_137, C_138) | ~m1_subset_1(C_138, A_136) | ~m1_subset_1(B_137, A_136) | v2_struct_0(k2_yellow_1(A_136)))), inference(resolution, [status(thm)], [c_260, c_65])).
% 3.30/1.53  tff(c_291, plain, (![B_142, C_143]: (r1_tarski(B_142, k10_lattice3(k2_yellow_1('#skF_2'), C_143, B_142)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_143, B_142), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_142, C_143), '#skF_2') | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(resolution, [status(thm)], [c_288, c_269])).
% 3.30/1.53  tff(c_302, plain, (![B_144, C_145]: (r1_tarski(B_144, k10_lattice3(k2_yellow_1('#skF_2'), C_145, B_144)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_145, B_144), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), '#skF_2') | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_287, c_62, c_291])).
% 3.30/1.53  tff(c_184, plain, (![C_131, B_132]: (k10_lattice3(k2_yellow_1('#skF_2'), C_131, B_132)=k10_lattice3(k2_yellow_1('#skF_2'), B_132, C_131) | ~m1_subset_1(C_131, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_180])).
% 3.30/1.53  tff(c_94, plain, (![A_91, C_92, B_93]: (r1_tarski(k2_xboole_0(A_91, C_92), B_93) | ~r1_tarski(C_92, B_93) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.53  tff(c_54, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.30/1.53  tff(c_98, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_94, c_54])).
% 3.30/1.53  tff(c_100, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.30/1.53  tff(c_205, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_184, c_100])).
% 3.30/1.53  tff(c_232, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_205])).
% 3.30/1.53  tff(c_305, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_302, c_232])).
% 3.30/1.53  tff(c_314, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_305])).
% 3.30/1.53  tff(c_330, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_314])).
% 3.30/1.53  tff(c_339, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_144, c_330])).
% 3.30/1.53  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_339])).
% 3.30/1.53  tff(c_348, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_314])).
% 3.30/1.53  tff(c_375, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_144, c_348])).
% 3.30/1.53  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_375])).
% 3.30/1.53  tff(c_380, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_98])).
% 3.30/1.53  tff(c_630, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_627, c_380])).
% 3.30/1.53  tff(c_639, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_630])).
% 3.30/1.53  tff(c_640, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_639])).
% 3.30/1.53  tff(c_643, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_529, c_640])).
% 3.30/1.53  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_643])).
% 3.30/1.53  tff(c_648, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_639])).
% 3.30/1.53  tff(c_652, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_529, c_648])).
% 3.30/1.53  tff(c_662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_652])).
% 3.30/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  Inference rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Ref     : 0
% 3.30/1.53  #Sup     : 123
% 3.30/1.53  #Fact    : 0
% 3.30/1.53  #Define  : 0
% 3.30/1.53  #Split   : 6
% 3.30/1.53  #Chain   : 0
% 3.30/1.53  #Close   : 0
% 3.30/1.53  
% 3.30/1.53  Ordering : KBO
% 3.30/1.53  
% 3.30/1.53  Simplification rules
% 3.30/1.53  ----------------------
% 3.30/1.53  #Subsume      : 18
% 3.30/1.53  #Demod        : 174
% 3.30/1.53  #Tautology    : 33
% 3.30/1.53  #SimpNegUnit  : 10
% 3.30/1.53  #BackRed      : 0
% 3.30/1.53  
% 3.30/1.53  #Partial instantiations: 0
% 3.30/1.53  #Strategies tried      : 1
% 3.30/1.53  
% 3.30/1.53  Timing (in seconds)
% 3.30/1.53  ----------------------
% 3.30/1.53  Preprocessing        : 0.37
% 3.30/1.53  Parsing              : 0.19
% 3.30/1.53  CNF conversion       : 0.03
% 3.30/1.53  Main loop            : 0.37
% 3.30/1.53  Inferencing          : 0.13
% 3.30/1.53  Reduction            : 0.12
% 3.30/1.53  Demodulation         : 0.09
% 3.30/1.53  BG Simplification    : 0.03
% 3.30/1.53  Subsumption          : 0.06
% 3.30/1.53  Abstraction          : 0.02
% 3.30/1.53  MUC search           : 0.00
% 3.30/1.53  Cooper               : 0.00
% 3.30/1.53  Total                : 0.79
% 3.30/1.53  Index Insertion      : 0.00
% 3.30/1.53  Index Deletion       : 0.00
% 3.30/1.53  Index Matching       : 0.00
% 3.30/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
