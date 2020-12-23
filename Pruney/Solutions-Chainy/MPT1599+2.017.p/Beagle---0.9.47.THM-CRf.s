%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 831 expanded)
%              Number of leaves         :   40 ( 336 expanded)
%              Depth                    :   14
%              Number of atoms          :  407 (2445 expanded)
%              Number of equality atoms :   23 ( 462 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_143,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_131,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_105,axiom,(
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

tff(f_119,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_93,axiom,(
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

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

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

tff(f_156,axiom,(
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

tff(c_46,plain,(
    ! [A_71] : u1_struct_0(k2_yellow_1(A_71)) = A_71 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_63,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_60,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    ! [A_69] : v5_orders_2(k2_yellow_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [A_68] : l1_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_492,plain,(
    ! [A_176,B_177,C_178] :
      ( k12_lattice3(A_176,B_177,C_178) = k11_lattice3(A_176,B_177,C_178)
      | ~ m1_subset_1(C_178,u1_struct_0(A_176))
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176)
      | ~ v2_lattice3(A_176)
      | ~ v5_orders_2(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_499,plain,(
    ! [A_71,B_177,C_178] :
      ( k12_lattice3(k2_yellow_1(A_71),B_177,C_178) = k11_lattice3(k2_yellow_1(A_71),B_177,C_178)
      | ~ m1_subset_1(C_178,A_71)
      | ~ m1_subset_1(B_177,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_492])).

tff(c_516,plain,(
    ! [A_182,B_183,C_184] :
      ( k12_lattice3(k2_yellow_1(A_182),B_183,C_184) = k11_lattice3(k2_yellow_1(A_182),B_183,C_184)
      | ~ m1_subset_1(C_184,A_182)
      | ~ m1_subset_1(B_183,A_182)
      | ~ v2_lattice3(k2_yellow_1(A_182)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_499])).

tff(c_520,plain,(
    ! [B_185,C_186] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_185,C_186) = k11_lattice3(k2_yellow_1('#skF_2'),B_185,C_186)
      | ~ m1_subset_1(C_186,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_516])).

tff(c_392,plain,(
    ! [A_156,B_157,C_158] :
      ( m1_subset_1(k12_lattice3(A_156,B_157,C_158),u1_struct_0(A_156))
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v2_lattice3(A_156)
      | ~ v5_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_395,plain,(
    ! [A_71,B_157,C_158] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_157,C_158),A_71)
      | ~ m1_subset_1(C_158,u1_struct_0(k2_yellow_1(A_71)))
      | ~ m1_subset_1(B_157,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_392])).

tff(c_397,plain,(
    ! [A_71,B_157,C_158] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_157,C_158),A_71)
      | ~ m1_subset_1(C_158,A_71)
      | ~ m1_subset_1(B_157,A_71)
      | ~ v2_lattice3(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_395])).

tff(c_526,plain,(
    ! [B_185,C_186] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_185,C_186),'#skF_2')
      | ~ m1_subset_1(C_186,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_186,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_397])).

tff(c_535,plain,(
    ! [B_185,C_186] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_185,C_186),'#skF_2')
      | ~ m1_subset_1(C_186,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_526])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_398,plain,(
    ! [A_159,C_160,B_161] :
      ( k11_lattice3(A_159,C_160,B_161) = k11_lattice3(A_159,B_161,C_160)
      | ~ m1_subset_1(C_160,u1_struct_0(A_159))
      | ~ m1_subset_1(B_161,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | ~ v2_lattice3(A_159)
      | ~ v5_orders_2(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_402,plain,(
    ! [A_71,C_160,B_161] :
      ( k11_lattice3(k2_yellow_1(A_71),C_160,B_161) = k11_lattice3(k2_yellow_1(A_71),B_161,C_160)
      | ~ m1_subset_1(C_160,A_71)
      | ~ m1_subset_1(B_161,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_398])).

tff(c_411,plain,(
    ! [A_165,C_166,B_167] :
      ( k11_lattice3(k2_yellow_1(A_165),C_166,B_167) = k11_lattice3(k2_yellow_1(A_165),B_167,C_166)
      | ~ m1_subset_1(C_166,A_165)
      | ~ m1_subset_1(B_167,A_165)
      | ~ v2_lattice3(k2_yellow_1(A_165)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_402])).

tff(c_414,plain,(
    ! [C_166,B_167] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_166,B_167) = k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_166)
      | ~ m1_subset_1(C_166,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_411])).

tff(c_556,plain,(
    ! [A_192,B_193,C_194] :
      ( r1_orders_2(A_192,k11_lattice3(A_192,B_193,C_194),C_194)
      | ~ m1_subset_1(k11_lattice3(A_192,B_193,C_194),u1_struct_0(A_192))
      | ~ m1_subset_1(C_194,u1_struct_0(A_192))
      | ~ m1_subset_1(B_193,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192)
      | ~ v2_lattice3(A_192)
      | ~ v5_orders_2(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_558,plain,(
    ! [B_167,C_166] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_166),C_166)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_166,B_167),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_166,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_166,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_556])).

tff(c_564,plain,(
    ! [B_167,C_166] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_166),C_166)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_166,B_167),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_166,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_558])).

tff(c_574,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_44,plain,(
    ! [A_70] :
      ( ~ v2_struct_0(k2_yellow_1(A_70))
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_577,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_574,c_44])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_577])).

tff(c_583,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_560,plain,(
    ! [C_166,B_167] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_166,B_167),B_167)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_166),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_166,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_166,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_556])).

tff(c_566,plain,(
    ! [C_166,B_167] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_166,B_167),B_167)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_166),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_166,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_560])).

tff(c_584,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_584])).

tff(c_588,plain,(
    ! [C_198,B_199] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_198,B_199),B_199)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_199,C_198),'#skF_2')
      | ~ m1_subset_1(C_198,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_36,plain,(
    ! [A_69] : v3_orders_2(k2_yellow_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_504,plain,(
    ! [A_179,B_180,C_181] :
      ( r3_orders_2(A_179,B_180,C_181)
      | ~ r1_orders_2(A_179,B_180,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | ~ v3_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_511,plain,(
    ! [A_71,B_180,C_181] :
      ( r3_orders_2(k2_yellow_1(A_71),B_180,C_181)
      | ~ r1_orders_2(k2_yellow_1(A_71),B_180,C_181)
      | ~ m1_subset_1(C_181,A_71)
      | ~ m1_subset_1(B_180,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v3_orders_2(k2_yellow_1(A_71))
      | v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_504])).

tff(c_546,plain,(
    ! [A_189,B_190,C_191] :
      ( r3_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ r1_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ m1_subset_1(C_191,A_189)
      | ~ m1_subset_1(B_190,A_189)
      | v2_struct_0(k2_yellow_1(A_189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_511])).

tff(c_52,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k2_yellow_1(A_72)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_72)))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_65,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_52])).

tff(c_555,plain,(
    ! [B_190,C_191,A_189] :
      ( r1_tarski(B_190,C_191)
      | v1_xboole_0(A_189)
      | ~ r1_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ m1_subset_1(C_191,A_189)
      | ~ m1_subset_1(B_190,A_189)
      | v2_struct_0(k2_yellow_1(A_189)) ) ),
    inference(resolution,[status(thm)],[c_546,c_65])).

tff(c_591,plain,(
    ! [C_198,B_199] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_198,B_199),B_199)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_198,B_199),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_199,C_198),'#skF_2')
      | ~ m1_subset_1(C_198,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_588,c_555])).

tff(c_629,plain,(
    ! [C_205,B_206] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_205,B_206),B_206)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_205,B_206),'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_206,C_205),'#skF_2')
      | ~ m1_subset_1(C_205,'#skF_2')
      | ~ m1_subset_1(B_206,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_62,c_591])).

tff(c_121,plain,(
    ! [A_108,B_109,C_110] :
      ( k12_lattice3(A_108,B_109,C_110) = k11_lattice3(A_108,B_109,C_110)
      | ~ m1_subset_1(C_110,u1_struct_0(A_108))
      | ~ m1_subset_1(B_109,u1_struct_0(A_108))
      | ~ l1_orders_2(A_108)
      | ~ v2_lattice3(A_108)
      | ~ v5_orders_2(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_128,plain,(
    ! [A_71,B_109,C_110] :
      ( k12_lattice3(k2_yellow_1(A_71),B_109,C_110) = k11_lattice3(k2_yellow_1(A_71),B_109,C_110)
      | ~ m1_subset_1(C_110,A_71)
      | ~ m1_subset_1(B_109,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_121])).

tff(c_133,plain,(
    ! [A_111,B_112,C_113] :
      ( k12_lattice3(k2_yellow_1(A_111),B_112,C_113) = k11_lattice3(k2_yellow_1(A_111),B_112,C_113)
      | ~ m1_subset_1(C_113,A_111)
      | ~ m1_subset_1(B_112,A_111)
      | ~ v2_lattice3(k2_yellow_1(A_111)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_128])).

tff(c_137,plain,(
    ! [B_114,C_115] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_114,C_115) = k11_lattice3(k2_yellow_1('#skF_2'),B_114,C_115)
      | ~ m1_subset_1(C_115,'#skF_2')
      | ~ m1_subset_1(B_114,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_114,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k12_lattice3(A_102,B_103,C_104),u1_struct_0(A_102))
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v2_lattice3(A_102)
      | ~ v5_orders_2(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,(
    ! [A_71,B_103,C_104] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_103,C_104),A_71)
      | ~ m1_subset_1(C_104,u1_struct_0(k2_yellow_1(A_71)))
      | ~ m1_subset_1(B_103,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_114])).

tff(c_119,plain,(
    ! [A_71,B_103,C_104] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_103,C_104),A_71)
      | ~ m1_subset_1(C_104,A_71)
      | ~ m1_subset_1(B_103,A_71)
      | ~ v2_lattice3(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_117])).

tff(c_143,plain,(
    ! [B_114,C_115] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_114,C_115),'#skF_2')
      | ~ m1_subset_1(C_115,'#skF_2')
      | ~ m1_subset_1(B_114,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_115,'#skF_2')
      | ~ m1_subset_1(B_114,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_119])).

tff(c_152,plain,(
    ! [B_114,C_115] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_114,C_115),'#skF_2')
      | ~ m1_subset_1(C_115,'#skF_2')
      | ~ m1_subset_1(B_114,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_143])).

tff(c_175,plain,(
    ! [A_127,C_128,B_129] :
      ( k11_lattice3(A_127,C_128,B_129) = k11_lattice3(A_127,B_129,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_127))
      | ~ m1_subset_1(B_129,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_182,plain,(
    ! [A_71,C_128,B_129] :
      ( k11_lattice3(k2_yellow_1(A_71),C_128,B_129) = k11_lattice3(k2_yellow_1(A_71),B_129,C_128)
      | ~ m1_subset_1(C_128,A_71)
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_175])).

tff(c_187,plain,(
    ! [A_130,C_131,B_132] :
      ( k11_lattice3(k2_yellow_1(A_130),C_131,B_132) = k11_lattice3(k2_yellow_1(A_130),B_132,C_131)
      | ~ m1_subset_1(C_131,A_130)
      | ~ m1_subset_1(B_132,A_130)
      | ~ v2_lattice3(k2_yellow_1(A_130)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_182])).

tff(c_190,plain,(
    ! [C_131,B_132] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_131,B_132) = k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_131)
      | ~ m1_subset_1(C_131,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_187])).

tff(c_270,plain,(
    ! [A_141,B_142,C_143] :
      ( r1_orders_2(A_141,k11_lattice3(A_141,B_142,C_143),C_143)
      | ~ m1_subset_1(k11_lattice3(A_141,B_142,C_143),u1_struct_0(A_141))
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_272,plain,(
    ! [B_132,C_131] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_131),C_131)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_131,B_132),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_131,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_132,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_131,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_270])).

tff(c_278,plain,(
    ! [B_132,C_131] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_131),C_131)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_131,B_132),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_131,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_272])).

tff(c_283,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_286,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_283,c_44])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_286])).

tff(c_292,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_293,plain,(
    ! [B_144,C_145] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),C_145)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_145,B_144),'#skF_2')
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_157,plain,(
    ! [A_118,B_119,C_120] :
      ( r3_orders_2(A_118,B_119,C_120)
      | ~ r1_orders_2(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_164,plain,(
    ! [A_71,B_119,C_120] :
      ( r3_orders_2(k2_yellow_1(A_71),B_119,C_120)
      | ~ r1_orders_2(k2_yellow_1(A_71),B_119,C_120)
      | ~ m1_subset_1(C_120,A_71)
      | ~ m1_subset_1(B_119,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v3_orders_2(k2_yellow_1(A_71))
      | v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_157])).

tff(c_169,plain,(
    ! [A_121,B_122,C_123] :
      ( r3_orders_2(k2_yellow_1(A_121),B_122,C_123)
      | ~ r1_orders_2(k2_yellow_1(A_121),B_122,C_123)
      | ~ m1_subset_1(C_123,A_121)
      | ~ m1_subset_1(B_122,A_121)
      | v2_struct_0(k2_yellow_1(A_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_164])).

tff(c_173,plain,(
    ! [B_122,C_123,A_121] :
      ( r1_tarski(B_122,C_123)
      | v1_xboole_0(A_121)
      | ~ r1_orders_2(k2_yellow_1(A_121),B_122,C_123)
      | ~ m1_subset_1(C_123,A_121)
      | ~ m1_subset_1(B_122,A_121)
      | v2_struct_0(k2_yellow_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_169,c_65])).

tff(c_296,plain,(
    ! [B_144,C_145] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),C_145)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_145,B_144),'#skF_2')
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_293,c_173])).

tff(c_307,plain,(
    ! [B_146,C_147] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),C_147)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_147,B_146),'#skF_2')
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_62,c_296])).

tff(c_191,plain,(
    ! [C_133,B_134] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_133,B_134) = k11_lattice3(k2_yellow_1('#skF_2'),B_134,C_133)
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_134,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_187])).

tff(c_102,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(A_93,k3_xboole_0(B_94,C_95))
      | ~ r1_tarski(A_93,C_95)
      | ~ r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_106,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_54])).

tff(c_108,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_212,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_108])).

tff(c_239,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_212])).

tff(c_310,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_307,c_239])).

tff(c_319,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_310])).

tff(c_335,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_344,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_152,c_335])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_344])).

tff(c_353,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_380,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_152,c_353])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_380])).

tff(c_385,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_632,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_629,c_385])).

tff(c_641,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_632])).

tff(c_642,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_645,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_535,c_642])).

tff(c_649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_645])).

tff(c_650,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_654,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_535,c_650])).

tff(c_664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:49:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.14/1.51  
% 3.14/1.51  %Foreground sorts:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Background operators:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Foreground operators:
% 3.14/1.51  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.14/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.51  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.14/1.51  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.14/1.51  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.14/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.51  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.14/1.51  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.14/1.51  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.51  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.51  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.14/1.51  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.14/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.14/1.51  
% 3.46/1.54  tff(f_143, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.46/1.54  tff(f_170, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.46/1.54  tff(f_131, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.46/1.54  tff(f_123, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.46/1.54  tff(f_105, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.46/1.54  tff(f_60, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 3.46/1.54  tff(f_119, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 3.46/1.54  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 3.46/1.54  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.46/1.54  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.46/1.54  tff(f_156, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.46/1.54  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.46/1.54  tff(c_46, plain, (![A_71]: (u1_struct_0(k2_yellow_1(A_71))=A_71)), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.46/1.54  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.46/1.54  tff(c_63, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 3.46/1.54  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.46/1.54  tff(c_64, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 3.46/1.54  tff(c_60, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.46/1.54  tff(c_40, plain, (![A_69]: (v5_orders_2(k2_yellow_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.46/1.54  tff(c_32, plain, (![A_68]: (l1_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.46/1.54  tff(c_492, plain, (![A_176, B_177, C_178]: (k12_lattice3(A_176, B_177, C_178)=k11_lattice3(A_176, B_177, C_178) | ~m1_subset_1(C_178, u1_struct_0(A_176)) | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~l1_orders_2(A_176) | ~v2_lattice3(A_176) | ~v5_orders_2(A_176))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.54  tff(c_499, plain, (![A_71, B_177, C_178]: (k12_lattice3(k2_yellow_1(A_71), B_177, C_178)=k11_lattice3(k2_yellow_1(A_71), B_177, C_178) | ~m1_subset_1(C_178, A_71) | ~m1_subset_1(B_177, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_492])).
% 3.46/1.54  tff(c_516, plain, (![A_182, B_183, C_184]: (k12_lattice3(k2_yellow_1(A_182), B_183, C_184)=k11_lattice3(k2_yellow_1(A_182), B_183, C_184) | ~m1_subset_1(C_184, A_182) | ~m1_subset_1(B_183, A_182) | ~v2_lattice3(k2_yellow_1(A_182)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_499])).
% 3.46/1.54  tff(c_520, plain, (![B_185, C_186]: (k12_lattice3(k2_yellow_1('#skF_2'), B_185, C_186)=k11_lattice3(k2_yellow_1('#skF_2'), B_185, C_186) | ~m1_subset_1(C_186, '#skF_2') | ~m1_subset_1(B_185, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_516])).
% 3.46/1.54  tff(c_392, plain, (![A_156, B_157, C_158]: (m1_subset_1(k12_lattice3(A_156, B_157, C_158), u1_struct_0(A_156)) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_157, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v2_lattice3(A_156) | ~v5_orders_2(A_156))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.54  tff(c_395, plain, (![A_71, B_157, C_158]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_157, C_158), A_71) | ~m1_subset_1(C_158, u1_struct_0(k2_yellow_1(A_71))) | ~m1_subset_1(B_157, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_392])).
% 3.46/1.54  tff(c_397, plain, (![A_71, B_157, C_158]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_157, C_158), A_71) | ~m1_subset_1(C_158, A_71) | ~m1_subset_1(B_157, A_71) | ~v2_lattice3(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_395])).
% 3.46/1.54  tff(c_526, plain, (![B_185, C_186]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_185, C_186), '#skF_2') | ~m1_subset_1(C_186, '#skF_2') | ~m1_subset_1(B_185, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_186, '#skF_2') | ~m1_subset_1(B_185, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_520, c_397])).
% 3.46/1.54  tff(c_535, plain, (![B_185, C_186]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_185, C_186), '#skF_2') | ~m1_subset_1(C_186, '#skF_2') | ~m1_subset_1(B_185, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_526])).
% 3.46/1.54  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.46/1.54  tff(c_398, plain, (![A_159, C_160, B_161]: (k11_lattice3(A_159, C_160, B_161)=k11_lattice3(A_159, B_161, C_160) | ~m1_subset_1(C_160, u1_struct_0(A_159)) | ~m1_subset_1(B_161, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | ~v2_lattice3(A_159) | ~v5_orders_2(A_159))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.46/1.54  tff(c_402, plain, (![A_71, C_160, B_161]: (k11_lattice3(k2_yellow_1(A_71), C_160, B_161)=k11_lattice3(k2_yellow_1(A_71), B_161, C_160) | ~m1_subset_1(C_160, A_71) | ~m1_subset_1(B_161, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_398])).
% 3.46/1.54  tff(c_411, plain, (![A_165, C_166, B_167]: (k11_lattice3(k2_yellow_1(A_165), C_166, B_167)=k11_lattice3(k2_yellow_1(A_165), B_167, C_166) | ~m1_subset_1(C_166, A_165) | ~m1_subset_1(B_167, A_165) | ~v2_lattice3(k2_yellow_1(A_165)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_402])).
% 3.46/1.54  tff(c_414, plain, (![C_166, B_167]: (k11_lattice3(k2_yellow_1('#skF_2'), C_166, B_167)=k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_166) | ~m1_subset_1(C_166, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_411])).
% 3.46/1.54  tff(c_556, plain, (![A_192, B_193, C_194]: (r1_orders_2(A_192, k11_lattice3(A_192, B_193, C_194), C_194) | ~m1_subset_1(k11_lattice3(A_192, B_193, C_194), u1_struct_0(A_192)) | ~m1_subset_1(C_194, u1_struct_0(A_192)) | ~m1_subset_1(B_193, u1_struct_0(A_192)) | ~l1_orders_2(A_192) | ~v2_lattice3(A_192) | ~v5_orders_2(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.46/1.54  tff(c_558, plain, (![B_167, C_166]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_166), C_166) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_166, B_167), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_166, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_166, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_556])).
% 3.46/1.54  tff(c_564, plain, (![B_167, C_166]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_166), C_166) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_166, B_167), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_166, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_558])).
% 3.46/1.54  tff(c_574, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_564])).
% 3.46/1.54  tff(c_44, plain, (![A_70]: (~v2_struct_0(k2_yellow_1(A_70)) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.46/1.54  tff(c_577, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_574, c_44])).
% 3.46/1.54  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_577])).
% 3.46/1.54  tff(c_583, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_564])).
% 3.46/1.54  tff(c_560, plain, (![C_166, B_167]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_166, B_167), B_167) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_166), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_166, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_166, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_556])).
% 3.46/1.54  tff(c_566, plain, (![C_166, B_167]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_166, B_167), B_167) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_166), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_166, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_560])).
% 3.46/1.54  tff(c_584, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_566])).
% 3.46/1.54  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_584])).
% 3.46/1.54  tff(c_588, plain, (![C_198, B_199]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_198, B_199), B_199) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_199, C_198), '#skF_2') | ~m1_subset_1(C_198, '#skF_2') | ~m1_subset_1(B_199, '#skF_2'))), inference(splitRight, [status(thm)], [c_566])).
% 3.46/1.54  tff(c_36, plain, (![A_69]: (v3_orders_2(k2_yellow_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.46/1.54  tff(c_504, plain, (![A_179, B_180, C_181]: (r3_orders_2(A_179, B_180, C_181) | ~r1_orders_2(A_179, B_180, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179) | ~v3_orders_2(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.54  tff(c_511, plain, (![A_71, B_180, C_181]: (r3_orders_2(k2_yellow_1(A_71), B_180, C_181) | ~r1_orders_2(k2_yellow_1(A_71), B_180, C_181) | ~m1_subset_1(C_181, A_71) | ~m1_subset_1(B_180, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v3_orders_2(k2_yellow_1(A_71)) | v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_504])).
% 3.46/1.54  tff(c_546, plain, (![A_189, B_190, C_191]: (r3_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~r1_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~m1_subset_1(C_191, A_189) | ~m1_subset_1(B_190, A_189) | v2_struct_0(k2_yellow_1(A_189)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_511])).
% 3.46/1.54  tff(c_52, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(k2_yellow_1(A_72))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_72))) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.46/1.54  tff(c_65, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_52])).
% 3.46/1.54  tff(c_555, plain, (![B_190, C_191, A_189]: (r1_tarski(B_190, C_191) | v1_xboole_0(A_189) | ~r1_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~m1_subset_1(C_191, A_189) | ~m1_subset_1(B_190, A_189) | v2_struct_0(k2_yellow_1(A_189)))), inference(resolution, [status(thm)], [c_546, c_65])).
% 3.46/1.54  tff(c_591, plain, (![C_198, B_199]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_198, B_199), B_199) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_198, B_199), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_199, C_198), '#skF_2') | ~m1_subset_1(C_198, '#skF_2') | ~m1_subset_1(B_199, '#skF_2'))), inference(resolution, [status(thm)], [c_588, c_555])).
% 3.46/1.54  tff(c_629, plain, (![C_205, B_206]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_205, B_206), B_206) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_205, B_206), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_206, C_205), '#skF_2') | ~m1_subset_1(C_205, '#skF_2') | ~m1_subset_1(B_206, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_583, c_62, c_591])).
% 3.46/1.54  tff(c_121, plain, (![A_108, B_109, C_110]: (k12_lattice3(A_108, B_109, C_110)=k11_lattice3(A_108, B_109, C_110) | ~m1_subset_1(C_110, u1_struct_0(A_108)) | ~m1_subset_1(B_109, u1_struct_0(A_108)) | ~l1_orders_2(A_108) | ~v2_lattice3(A_108) | ~v5_orders_2(A_108))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.46/1.54  tff(c_128, plain, (![A_71, B_109, C_110]: (k12_lattice3(k2_yellow_1(A_71), B_109, C_110)=k11_lattice3(k2_yellow_1(A_71), B_109, C_110) | ~m1_subset_1(C_110, A_71) | ~m1_subset_1(B_109, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_121])).
% 3.46/1.54  tff(c_133, plain, (![A_111, B_112, C_113]: (k12_lattice3(k2_yellow_1(A_111), B_112, C_113)=k11_lattice3(k2_yellow_1(A_111), B_112, C_113) | ~m1_subset_1(C_113, A_111) | ~m1_subset_1(B_112, A_111) | ~v2_lattice3(k2_yellow_1(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_128])).
% 3.46/1.54  tff(c_137, plain, (![B_114, C_115]: (k12_lattice3(k2_yellow_1('#skF_2'), B_114, C_115)=k11_lattice3(k2_yellow_1('#skF_2'), B_114, C_115) | ~m1_subset_1(C_115, '#skF_2') | ~m1_subset_1(B_114, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_133])).
% 3.46/1.54  tff(c_114, plain, (![A_102, B_103, C_104]: (m1_subset_1(k12_lattice3(A_102, B_103, C_104), u1_struct_0(A_102)) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v2_lattice3(A_102) | ~v5_orders_2(A_102))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.54  tff(c_117, plain, (![A_71, B_103, C_104]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_103, C_104), A_71) | ~m1_subset_1(C_104, u1_struct_0(k2_yellow_1(A_71))) | ~m1_subset_1(B_103, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_114])).
% 3.46/1.54  tff(c_119, plain, (![A_71, B_103, C_104]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_103, C_104), A_71) | ~m1_subset_1(C_104, A_71) | ~m1_subset_1(B_103, A_71) | ~v2_lattice3(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_117])).
% 3.46/1.54  tff(c_143, plain, (![B_114, C_115]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_114, C_115), '#skF_2') | ~m1_subset_1(C_115, '#skF_2') | ~m1_subset_1(B_114, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_115, '#skF_2') | ~m1_subset_1(B_114, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_119])).
% 3.46/1.54  tff(c_152, plain, (![B_114, C_115]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_114, C_115), '#skF_2') | ~m1_subset_1(C_115, '#skF_2') | ~m1_subset_1(B_114, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_143])).
% 3.46/1.54  tff(c_175, plain, (![A_127, C_128, B_129]: (k11_lattice3(A_127, C_128, B_129)=k11_lattice3(A_127, B_129, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_127)) | ~m1_subset_1(B_129, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.46/1.54  tff(c_182, plain, (![A_71, C_128, B_129]: (k11_lattice3(k2_yellow_1(A_71), C_128, B_129)=k11_lattice3(k2_yellow_1(A_71), B_129, C_128) | ~m1_subset_1(C_128, A_71) | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_175])).
% 3.46/1.54  tff(c_187, plain, (![A_130, C_131, B_132]: (k11_lattice3(k2_yellow_1(A_130), C_131, B_132)=k11_lattice3(k2_yellow_1(A_130), B_132, C_131) | ~m1_subset_1(C_131, A_130) | ~m1_subset_1(B_132, A_130) | ~v2_lattice3(k2_yellow_1(A_130)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_182])).
% 3.46/1.54  tff(c_190, plain, (![C_131, B_132]: (k11_lattice3(k2_yellow_1('#skF_2'), C_131, B_132)=k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_131) | ~m1_subset_1(C_131, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_187])).
% 3.46/1.54  tff(c_270, plain, (![A_141, B_142, C_143]: (r1_orders_2(A_141, k11_lattice3(A_141, B_142, C_143), C_143) | ~m1_subset_1(k11_lattice3(A_141, B_142, C_143), u1_struct_0(A_141)) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.46/1.54  tff(c_272, plain, (![B_132, C_131]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_131), C_131) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_131, B_132), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_131, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_132, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_131, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_270])).
% 3.46/1.54  tff(c_278, plain, (![B_132, C_131]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_131), C_131) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_131, B_132), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_131, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_272])).
% 3.46/1.54  tff(c_283, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_278])).
% 3.46/1.54  tff(c_286, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_283, c_44])).
% 3.46/1.54  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_286])).
% 3.46/1.54  tff(c_292, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_278])).
% 3.46/1.54  tff(c_293, plain, (![B_144, C_145]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), C_145) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_145, B_144), '#skF_2') | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(splitRight, [status(thm)], [c_278])).
% 3.46/1.54  tff(c_157, plain, (![A_118, B_119, C_120]: (r3_orders_2(A_118, B_119, C_120) | ~r1_orders_2(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.54  tff(c_164, plain, (![A_71, B_119, C_120]: (r3_orders_2(k2_yellow_1(A_71), B_119, C_120) | ~r1_orders_2(k2_yellow_1(A_71), B_119, C_120) | ~m1_subset_1(C_120, A_71) | ~m1_subset_1(B_119, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v3_orders_2(k2_yellow_1(A_71)) | v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_157])).
% 3.46/1.54  tff(c_169, plain, (![A_121, B_122, C_123]: (r3_orders_2(k2_yellow_1(A_121), B_122, C_123) | ~r1_orders_2(k2_yellow_1(A_121), B_122, C_123) | ~m1_subset_1(C_123, A_121) | ~m1_subset_1(B_122, A_121) | v2_struct_0(k2_yellow_1(A_121)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_164])).
% 3.46/1.54  tff(c_173, plain, (![B_122, C_123, A_121]: (r1_tarski(B_122, C_123) | v1_xboole_0(A_121) | ~r1_orders_2(k2_yellow_1(A_121), B_122, C_123) | ~m1_subset_1(C_123, A_121) | ~m1_subset_1(B_122, A_121) | v2_struct_0(k2_yellow_1(A_121)))), inference(resolution, [status(thm)], [c_169, c_65])).
% 3.46/1.54  tff(c_296, plain, (![B_144, C_145]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), C_145) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_145, B_144), '#skF_2') | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(resolution, [status(thm)], [c_293, c_173])).
% 3.46/1.54  tff(c_307, plain, (![B_146, C_147]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), C_147) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_147, B_146), '#skF_2') | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_292, c_62, c_296])).
% 3.46/1.54  tff(c_191, plain, (![C_133, B_134]: (k11_lattice3(k2_yellow_1('#skF_2'), C_133, B_134)=k11_lattice3(k2_yellow_1('#skF_2'), B_134, C_133) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_134, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_187])).
% 3.46/1.54  tff(c_102, plain, (![A_93, B_94, C_95]: (r1_tarski(A_93, k3_xboole_0(B_94, C_95)) | ~r1_tarski(A_93, C_95) | ~r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.54  tff(c_54, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.46/1.54  tff(c_106, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_102, c_54])).
% 3.46/1.54  tff(c_108, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_106])).
% 3.46/1.54  tff(c_212, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_191, c_108])).
% 3.46/1.54  tff(c_239, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_212])).
% 3.46/1.54  tff(c_310, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_307, c_239])).
% 3.46/1.54  tff(c_319, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_310])).
% 3.46/1.54  tff(c_335, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_319])).
% 3.46/1.54  tff(c_344, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_152, c_335])).
% 3.46/1.54  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_344])).
% 3.46/1.54  tff(c_353, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 3.46/1.54  tff(c_380, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_152, c_353])).
% 3.46/1.54  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_380])).
% 3.46/1.54  tff(c_385, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 3.46/1.54  tff(c_632, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_629, c_385])).
% 3.46/1.54  tff(c_641, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_632])).
% 3.46/1.54  tff(c_642, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_641])).
% 3.46/1.54  tff(c_645, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_535, c_642])).
% 3.46/1.54  tff(c_649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_645])).
% 3.46/1.54  tff(c_650, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_641])).
% 3.46/1.54  tff(c_654, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_535, c_650])).
% 3.46/1.54  tff(c_664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_654])).
% 3.46/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  Inference rules
% 3.46/1.54  ----------------------
% 3.46/1.54  #Ref     : 0
% 3.46/1.54  #Sup     : 123
% 3.46/1.54  #Fact    : 0
% 3.46/1.54  #Define  : 0
% 3.46/1.54  #Split   : 6
% 3.46/1.54  #Chain   : 0
% 3.46/1.54  #Close   : 0
% 3.46/1.54  
% 3.46/1.54  Ordering : KBO
% 3.46/1.54  
% 3.46/1.54  Simplification rules
% 3.46/1.54  ----------------------
% 3.46/1.54  #Subsume      : 18
% 3.46/1.54  #Demod        : 170
% 3.46/1.54  #Tautology    : 35
% 3.46/1.54  #SimpNegUnit  : 12
% 3.46/1.54  #BackRed      : 0
% 3.46/1.54  
% 3.46/1.54  #Partial instantiations: 0
% 3.46/1.54  #Strategies tried      : 1
% 3.46/1.54  
% 3.46/1.54  Timing (in seconds)
% 3.46/1.54  ----------------------
% 3.46/1.55  Preprocessing        : 0.37
% 3.46/1.55  Parsing              : 0.19
% 3.46/1.55  CNF conversion       : 0.03
% 3.46/1.55  Main loop            : 0.40
% 3.46/1.55  Inferencing          : 0.14
% 3.46/1.55  Reduction            : 0.13
% 3.46/1.55  Demodulation         : 0.10
% 3.46/1.55  BG Simplification    : 0.03
% 3.46/1.55  Subsumption          : 0.07
% 3.46/1.55  Abstraction          : 0.02
% 3.46/1.55  MUC search           : 0.00
% 3.46/1.55  Cooper               : 0.00
% 3.46/1.55  Total                : 0.82
% 3.46/1.55  Index Insertion      : 0.00
% 3.46/1.55  Index Deletion       : 0.00
% 3.46/1.55  Index Matching       : 0.00
% 3.46/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
