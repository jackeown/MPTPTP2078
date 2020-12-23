%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:21 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 423 expanded)
%              Number of leaves         :   38 ( 176 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 (1229 expanded)
%              Number of equality atoms :   20 ( 201 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_137,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_133,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_121,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_150,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_42,plain,(
    ! [A_69] : u1_struct_0(k2_yellow_1(A_69)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_59,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_56,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    ! [A_68] : v5_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_32,plain,(
    ! [A_67] : l1_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_392,plain,(
    ! [A_175,B_176,C_177] :
      ( k13_lattice3(A_175,B_176,C_177) = k10_lattice3(A_175,B_176,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v1_lattice3(A_175)
      | ~ v5_orders_2(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_399,plain,(
    ! [A_69,B_176,C_177] :
      ( k13_lattice3(k2_yellow_1(A_69),B_176,C_177) = k10_lattice3(k2_yellow_1(A_69),B_176,C_177)
      | ~ m1_subset_1(C_177,A_69)
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v1_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_392])).

tff(c_415,plain,(
    ! [A_181,B_182,C_183] :
      ( k13_lattice3(k2_yellow_1(A_181),B_182,C_183) = k10_lattice3(k2_yellow_1(A_181),B_182,C_183)
      | ~ m1_subset_1(C_183,A_181)
      | ~ m1_subset_1(B_182,A_181)
      | ~ v1_lattice3(k2_yellow_1(A_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_399])).

tff(c_419,plain,(
    ! [B_184,C_185] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_184,C_185) = k10_lattice3(k2_yellow_1('#skF_2'),B_184,C_185)
      | ~ m1_subset_1(C_185,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_415])).

tff(c_367,plain,(
    ! [A_160,B_161,C_162] :
      ( m1_subset_1(k13_lattice3(A_160,B_161,C_162),u1_struct_0(A_160))
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_orders_2(A_160)
      | ~ v1_lattice3(A_160)
      | ~ v5_orders_2(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_370,plain,(
    ! [A_69,B_161,C_162] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_69),B_161,C_162),A_69)
      | ~ m1_subset_1(C_162,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_161,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v1_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_367])).

tff(c_372,plain,(
    ! [A_69,B_161,C_162] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_69),B_161,C_162),A_69)
      | ~ m1_subset_1(C_162,A_69)
      | ~ m1_subset_1(B_161,A_69)
      | ~ v1_lattice3(k2_yellow_1(A_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_42,c_370])).

tff(c_425,plain,(
    ! [B_184,C_185] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_184,C_185),'#skF_2')
      | ~ m1_subset_1(C_185,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_185,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_372])).

tff(c_434,plain,(
    ! [B_184,C_185] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_184,C_185),'#skF_2')
      | ~ m1_subset_1(C_185,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_425])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_418,plain,(
    ! [B_182,C_183] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_182,C_183) = k10_lattice3(k2_yellow_1('#skF_2'),B_182,C_183)
      | ~ m1_subset_1(C_183,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_415])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k13_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v1_lattice3(A_8)
      | ~ v5_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_536,plain,(
    ! [A_199,C_200,B_201] :
      ( r1_orders_2(A_199,C_200,k13_lattice3(A_199,B_201,C_200))
      | ~ m1_subset_1(k13_lattice3(A_199,B_201,C_200),u1_struct_0(A_199))
      | ~ m1_subset_1(C_200,u1_struct_0(A_199))
      | ~ m1_subset_1(B_201,u1_struct_0(A_199))
      | ~ l1_orders_2(A_199)
      | ~ v1_lattice3(A_199)
      | ~ v5_orders_2(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_548,plain,(
    ! [A_202,C_203,B_204] :
      ( r1_orders_2(A_202,C_203,k13_lattice3(A_202,B_204,C_203))
      | ~ m1_subset_1(C_203,u1_struct_0(A_202))
      | ~ m1_subset_1(B_204,u1_struct_0(A_202))
      | ~ l1_orders_2(A_202)
      | ~ v1_lattice3(A_202)
      | ~ v5_orders_2(A_202) ) ),
    inference(resolution,[status(thm)],[c_10,c_536])).

tff(c_555,plain,(
    ! [C_183,B_182] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_183,k10_lattice3(k2_yellow_1('#skF_2'),B_182,C_183))
      | ~ m1_subset_1(C_183,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_182,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_183,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_548])).

tff(c_561,plain,(
    ! [C_205,B_206] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_205,k10_lattice3(k2_yellow_1('#skF_2'),B_206,C_205))
      | ~ m1_subset_1(C_205,'#skF_2')
      | ~ m1_subset_1(B_206,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_32,c_42,c_42,c_555])).

tff(c_36,plain,(
    ! [A_68] : v3_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_374,plain,(
    ! [A_166,B_167,C_168] :
      ( r3_orders_2(A_166,B_167,C_168)
      | ~ r1_orders_2(A_166,B_167,C_168)
      | ~ m1_subset_1(C_168,u1_struct_0(A_166))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_orders_2(A_166)
      | ~ v3_orders_2(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_381,plain,(
    ! [A_69,B_167,C_168] :
      ( r3_orders_2(k2_yellow_1(A_69),B_167,C_168)
      | ~ r1_orders_2(k2_yellow_1(A_69),B_167,C_168)
      | ~ m1_subset_1(C_168,A_69)
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v3_orders_2(k2_yellow_1(A_69))
      | v2_struct_0(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_374])).

tff(c_386,plain,(
    ! [A_169,B_170,C_171] :
      ( r3_orders_2(k2_yellow_1(A_169),B_170,C_171)
      | ~ r1_orders_2(k2_yellow_1(A_169),B_170,C_171)
      | ~ m1_subset_1(C_171,A_169)
      | ~ m1_subset_1(B_170,A_169)
      | v2_struct_0(k2_yellow_1(A_169)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_42,c_381])).

tff(c_48,plain,(
    ! [B_74,C_76,A_70] :
      ( r1_tarski(B_74,C_76)
      | ~ r3_orders_2(k2_yellow_1(A_70),B_74,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(k2_yellow_1(A_70)))
      | ~ m1_subset_1(B_74,u1_struct_0(k2_yellow_1(A_70)))
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_61,plain,(
    ! [B_74,C_76,A_70] :
      ( r1_tarski(B_74,C_76)
      | ~ r3_orders_2(k2_yellow_1(A_70),B_74,C_76)
      | ~ m1_subset_1(C_76,A_70)
      | ~ m1_subset_1(B_74,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_48])).

tff(c_390,plain,(
    ! [B_170,C_171,A_169] :
      ( r1_tarski(B_170,C_171)
      | v1_xboole_0(A_169)
      | ~ r1_orders_2(k2_yellow_1(A_169),B_170,C_171)
      | ~ m1_subset_1(C_171,A_169)
      | ~ m1_subset_1(B_170,A_169)
      | v2_struct_0(k2_yellow_1(A_169)) ) ),
    inference(resolution,[status(thm)],[c_386,c_61])).

tff(c_564,plain,(
    ! [C_205,B_206] :
      ( r1_tarski(C_205,k10_lattice3(k2_yellow_1('#skF_2'),B_206,C_205))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_206,C_205),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_205,'#skF_2')
      | ~ m1_subset_1(B_206,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_561,c_390])).

tff(c_573,plain,(
    ! [C_205,B_206] :
      ( r1_tarski(C_205,k10_lattice3(k2_yellow_1('#skF_2'),B_206,C_205))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_206,C_205),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_205,'#skF_2')
      | ~ m1_subset_1(B_206,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_564])).

tff(c_587,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_590,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_587,c_8])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_590])).

tff(c_597,plain,(
    ! [C_209,B_210] :
      ( r1_tarski(C_209,k10_lattice3(k2_yellow_1('#skF_2'),B_210,C_209))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_210,C_209),'#skF_2')
      | ~ m1_subset_1(C_209,'#skF_2')
      | ~ m1_subset_1(B_210,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_141,plain,(
    ! [A_119,B_120,C_121] :
      ( k13_lattice3(A_119,B_120,C_121) = k10_lattice3(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v1_lattice3(A_119)
      | ~ v5_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_148,plain,(
    ! [A_69,B_120,C_121] :
      ( k13_lattice3(k2_yellow_1(A_69),B_120,C_121) = k10_lattice3(k2_yellow_1(A_69),B_120,C_121)
      | ~ m1_subset_1(C_121,A_69)
      | ~ m1_subset_1(B_120,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v1_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_153,plain,(
    ! [A_122,B_123,C_124] :
      ( k13_lattice3(k2_yellow_1(A_122),B_123,C_124) = k10_lattice3(k2_yellow_1(A_122),B_123,C_124)
      | ~ m1_subset_1(C_124,A_122)
      | ~ m1_subset_1(B_123,A_122)
      | ~ v1_lattice3(k2_yellow_1(A_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_148])).

tff(c_157,plain,(
    ! [B_125,C_126] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_125,C_126) = k10_lattice3(k2_yellow_1('#skF_2'),B_125,C_126)
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_153])).

tff(c_100,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k13_lattice3(A_98,B_99,C_100),u1_struct_0(A_98))
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v1_lattice3(A_98)
      | ~ v5_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    ! [A_69,B_99,C_100] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_69),B_99,C_100),A_69)
      | ~ m1_subset_1(C_100,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v1_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_100])).

tff(c_105,plain,(
    ! [A_69,B_99,C_100] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_69),B_99,C_100),A_69)
      | ~ m1_subset_1(C_100,A_69)
      | ~ m1_subset_1(B_99,A_69)
      | ~ v1_lattice3(k2_yellow_1(A_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_42,c_103])).

tff(c_163,plain,(
    ! [B_125,C_126] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_125,C_126),'#skF_2')
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_105])).

tff(c_172,plain,(
    ! [B_125,C_126] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_125,C_126),'#skF_2')
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_125,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_163])).

tff(c_156,plain,(
    ! [B_123,C_124] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_123,C_124) = k10_lattice3(k2_yellow_1('#skF_2'),B_123,C_124)
      | ~ m1_subset_1(C_124,'#skF_2')
      | ~ m1_subset_1(B_123,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_153])).

tff(c_252,plain,(
    ! [A_137,C_138,B_139] :
      ( r1_orders_2(A_137,C_138,k13_lattice3(A_137,B_139,C_138))
      | ~ m1_subset_1(k13_lattice3(A_137,B_139,C_138),u1_struct_0(A_137))
      | ~ m1_subset_1(C_138,u1_struct_0(A_137))
      | ~ m1_subset_1(B_139,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v1_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_268,plain,(
    ! [A_140,C_141,B_142] :
      ( r1_orders_2(A_140,C_141,k13_lattice3(A_140,B_142,C_141))
      | ~ m1_subset_1(C_141,u1_struct_0(A_140))
      | ~ m1_subset_1(B_142,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v1_lattice3(A_140)
      | ~ v5_orders_2(A_140) ) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_275,plain,(
    ! [C_124,B_123] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_124,k10_lattice3(k2_yellow_1('#skF_2'),B_123,C_124))
      | ~ m1_subset_1(C_124,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_123,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_124,'#skF_2')
      | ~ m1_subset_1(B_123,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_268])).

tff(c_281,plain,(
    ! [C_143,B_144] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_143,k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_143))
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_32,c_42,c_42,c_275])).

tff(c_106,plain,(
    ! [A_101,B_102,C_103] :
      ( r3_orders_2(A_101,B_102,C_103)
      | ~ r1_orders_2(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [A_69,B_102,C_103] :
      ( r3_orders_2(k2_yellow_1(A_69),B_102,C_103)
      | ~ r1_orders_2(k2_yellow_1(A_69),B_102,C_103)
      | ~ m1_subset_1(C_103,A_69)
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v3_orders_2(k2_yellow_1(A_69))
      | v2_struct_0(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_119,plain,(
    ! [A_107,B_108,C_109] :
      ( r3_orders_2(k2_yellow_1(A_107),B_108,C_109)
      | ~ r1_orders_2(k2_yellow_1(A_107),B_108,C_109)
      | ~ m1_subset_1(C_109,A_107)
      | ~ m1_subset_1(B_108,A_107)
      | v2_struct_0(k2_yellow_1(A_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_42,c_110])).

tff(c_123,plain,(
    ! [B_108,C_109,A_107] :
      ( r1_tarski(B_108,C_109)
      | v1_xboole_0(A_107)
      | ~ r1_orders_2(k2_yellow_1(A_107),B_108,C_109)
      | ~ m1_subset_1(C_109,A_107)
      | ~ m1_subset_1(B_108,A_107)
      | v2_struct_0(k2_yellow_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_119,c_61])).

tff(c_284,plain,(
    ! [C_143,B_144] :
      ( r1_tarski(C_143,k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_143))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_143),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_281,c_123])).

tff(c_293,plain,(
    ! [C_143,B_144] :
      ( r1_tarski(C_143,k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_143))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_144,C_143),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_143,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_284])).

tff(c_317,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_320,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_317,c_8])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_320])).

tff(c_339,plain,(
    ! [C_152,B_153] :
      ( r1_tarski(C_152,k10_lattice3(k2_yellow_1('#skF_2'),B_153,C_152))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_153,C_152),'#skF_2')
      | ~ m1_subset_1(C_152,'#skF_2')
      | ~ m1_subset_1(B_153,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_177,plain,(
    ! [A_129,C_130,B_131] :
      ( k10_lattice3(A_129,C_130,B_131) = k10_lattice3(A_129,B_131,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_129))
      | ~ m1_subset_1(B_131,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v1_lattice3(A_129)
      | ~ v5_orders_2(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,(
    ! [A_69,C_130,B_131] :
      ( k10_lattice3(k2_yellow_1(A_69),C_130,B_131) = k10_lattice3(k2_yellow_1(A_69),B_131,C_130)
      | ~ m1_subset_1(C_130,A_69)
      | ~ m1_subset_1(B_131,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v1_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_177])).

tff(c_189,plain,(
    ! [A_132,C_133,B_134] :
      ( k10_lattice3(k2_yellow_1(A_132),C_133,B_134) = k10_lattice3(k2_yellow_1(A_132),B_134,C_133)
      | ~ m1_subset_1(C_133,A_132)
      | ~ m1_subset_1(B_134,A_132)
      | ~ v1_lattice3(k2_yellow_1(A_132)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_184])).

tff(c_193,plain,(
    ! [C_135,B_136] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_135,B_136) = k10_lattice3(k2_yellow_1('#skF_2'),B_136,C_135)
      | ~ m1_subset_1(C_135,'#skF_2')
      | ~ m1_subset_1(B_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_189])).

tff(c_88,plain,(
    ! [A_89,C_90,B_91] :
      ( r1_tarski(k2_xboole_0(A_89,C_90),B_91)
      | ~ r1_tarski(C_90,B_91)
      | ~ r1_tarski(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_92,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_50])).

tff(c_93,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_214,plain,
    ( ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_93])).

tff(c_241,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_214])).

tff(c_342,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_339,c_241])).

tff(c_351,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_342])).

tff(c_354,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_172,c_351])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_354])).

tff(c_359,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_600,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_597,c_359])).

tff(c_609,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_600])).

tff(c_618,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_434,c_609])).

tff(c_626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  
% 2.94/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.48  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.94/1.48  
% 2.94/1.48  %Foreground sorts:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Background operators:
% 2.94/1.48  
% 2.94/1.48  
% 2.94/1.48  %Foreground operators:
% 2.94/1.48  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.94/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.48  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.94/1.48  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.48  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 2.94/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.94/1.48  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.94/1.48  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.94/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.48  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.94/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.48  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.94/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.94/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.48  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.94/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.48  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.94/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.94/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.48  
% 2.94/1.50  tff(f_137, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.94/1.50  tff(f_164, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 2.94/1.50  tff(f_133, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.94/1.50  tff(f_125, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.94/1.50  tff(f_77, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 2.94/1.50  tff(f_65, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 2.94/1.50  tff(f_121, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 2.94/1.50  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.94/1.50  tff(f_150, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.94/1.50  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.94/1.50  tff(f_91, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 2.94/1.50  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.94/1.50  tff(c_42, plain, (![A_69]: (u1_struct_0(k2_yellow_1(A_69))=A_69)), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.94/1.50  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.94/1.50  tff(c_59, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 2.94/1.50  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.94/1.50  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 2.94/1.50  tff(c_56, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.94/1.50  tff(c_40, plain, (![A_68]: (v5_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.94/1.50  tff(c_32, plain, (![A_67]: (l1_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.94/1.50  tff(c_392, plain, (![A_175, B_176, C_177]: (k13_lattice3(A_175, B_176, C_177)=k10_lattice3(A_175, B_176, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v1_lattice3(A_175) | ~v5_orders_2(A_175))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.50  tff(c_399, plain, (![A_69, B_176, C_177]: (k13_lattice3(k2_yellow_1(A_69), B_176, C_177)=k10_lattice3(k2_yellow_1(A_69), B_176, C_177) | ~m1_subset_1(C_177, A_69) | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v1_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_392])).
% 2.94/1.50  tff(c_415, plain, (![A_181, B_182, C_183]: (k13_lattice3(k2_yellow_1(A_181), B_182, C_183)=k10_lattice3(k2_yellow_1(A_181), B_182, C_183) | ~m1_subset_1(C_183, A_181) | ~m1_subset_1(B_182, A_181) | ~v1_lattice3(k2_yellow_1(A_181)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_399])).
% 2.94/1.50  tff(c_419, plain, (![B_184, C_185]: (k13_lattice3(k2_yellow_1('#skF_2'), B_184, C_185)=k10_lattice3(k2_yellow_1('#skF_2'), B_184, C_185) | ~m1_subset_1(C_185, '#skF_2') | ~m1_subset_1(B_184, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_415])).
% 2.94/1.50  tff(c_367, plain, (![A_160, B_161, C_162]: (m1_subset_1(k13_lattice3(A_160, B_161, C_162), u1_struct_0(A_160)) | ~m1_subset_1(C_162, u1_struct_0(A_160)) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_orders_2(A_160) | ~v1_lattice3(A_160) | ~v5_orders_2(A_160))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.50  tff(c_370, plain, (![A_69, B_161, C_162]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_69), B_161, C_162), A_69) | ~m1_subset_1(C_162, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_161, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v1_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_367])).
% 2.94/1.50  tff(c_372, plain, (![A_69, B_161, C_162]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_69), B_161, C_162), A_69) | ~m1_subset_1(C_162, A_69) | ~m1_subset_1(B_161, A_69) | ~v1_lattice3(k2_yellow_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_42, c_370])).
% 2.94/1.50  tff(c_425, plain, (![B_184, C_185]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_184, C_185), '#skF_2') | ~m1_subset_1(C_185, '#skF_2') | ~m1_subset_1(B_184, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_185, '#skF_2') | ~m1_subset_1(B_184, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_419, c_372])).
% 2.94/1.50  tff(c_434, plain, (![B_184, C_185]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_184, C_185), '#skF_2') | ~m1_subset_1(C_185, '#skF_2') | ~m1_subset_1(B_184, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_425])).
% 2.94/1.50  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.94/1.50  tff(c_418, plain, (![B_182, C_183]: (k13_lattice3(k2_yellow_1('#skF_2'), B_182, C_183)=k10_lattice3(k2_yellow_1('#skF_2'), B_182, C_183) | ~m1_subset_1(C_183, '#skF_2') | ~m1_subset_1(B_182, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_415])).
% 2.94/1.50  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k13_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v1_lattice3(A_8) | ~v5_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.50  tff(c_536, plain, (![A_199, C_200, B_201]: (r1_orders_2(A_199, C_200, k13_lattice3(A_199, B_201, C_200)) | ~m1_subset_1(k13_lattice3(A_199, B_201, C_200), u1_struct_0(A_199)) | ~m1_subset_1(C_200, u1_struct_0(A_199)) | ~m1_subset_1(B_201, u1_struct_0(A_199)) | ~l1_orders_2(A_199) | ~v1_lattice3(A_199) | ~v5_orders_2(A_199))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.94/1.50  tff(c_548, plain, (![A_202, C_203, B_204]: (r1_orders_2(A_202, C_203, k13_lattice3(A_202, B_204, C_203)) | ~m1_subset_1(C_203, u1_struct_0(A_202)) | ~m1_subset_1(B_204, u1_struct_0(A_202)) | ~l1_orders_2(A_202) | ~v1_lattice3(A_202) | ~v5_orders_2(A_202))), inference(resolution, [status(thm)], [c_10, c_536])).
% 2.94/1.50  tff(c_555, plain, (![C_183, B_182]: (r1_orders_2(k2_yellow_1('#skF_2'), C_183, k10_lattice3(k2_yellow_1('#skF_2'), B_182, C_183)) | ~m1_subset_1(C_183, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_182, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_183, '#skF_2') | ~m1_subset_1(B_182, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_548])).
% 2.94/1.50  tff(c_561, plain, (![C_205, B_206]: (r1_orders_2(k2_yellow_1('#skF_2'), C_205, k10_lattice3(k2_yellow_1('#skF_2'), B_206, C_205)) | ~m1_subset_1(C_205, '#skF_2') | ~m1_subset_1(B_206, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_32, c_42, c_42, c_555])).
% 2.94/1.50  tff(c_36, plain, (![A_68]: (v3_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.94/1.50  tff(c_374, plain, (![A_166, B_167, C_168]: (r3_orders_2(A_166, B_167, C_168) | ~r1_orders_2(A_166, B_167, C_168) | ~m1_subset_1(C_168, u1_struct_0(A_166)) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_orders_2(A_166) | ~v3_orders_2(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.94/1.50  tff(c_381, plain, (![A_69, B_167, C_168]: (r3_orders_2(k2_yellow_1(A_69), B_167, C_168) | ~r1_orders_2(k2_yellow_1(A_69), B_167, C_168) | ~m1_subset_1(C_168, A_69) | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v3_orders_2(k2_yellow_1(A_69)) | v2_struct_0(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_374])).
% 2.94/1.50  tff(c_386, plain, (![A_169, B_170, C_171]: (r3_orders_2(k2_yellow_1(A_169), B_170, C_171) | ~r1_orders_2(k2_yellow_1(A_169), B_170, C_171) | ~m1_subset_1(C_171, A_169) | ~m1_subset_1(B_170, A_169) | v2_struct_0(k2_yellow_1(A_169)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_42, c_381])).
% 2.94/1.51  tff(c_48, plain, (![B_74, C_76, A_70]: (r1_tarski(B_74, C_76) | ~r3_orders_2(k2_yellow_1(A_70), B_74, C_76) | ~m1_subset_1(C_76, u1_struct_0(k2_yellow_1(A_70))) | ~m1_subset_1(B_74, u1_struct_0(k2_yellow_1(A_70))) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.94/1.51  tff(c_61, plain, (![B_74, C_76, A_70]: (r1_tarski(B_74, C_76) | ~r3_orders_2(k2_yellow_1(A_70), B_74, C_76) | ~m1_subset_1(C_76, A_70) | ~m1_subset_1(B_74, A_70) | v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_48])).
% 2.94/1.51  tff(c_390, plain, (![B_170, C_171, A_169]: (r1_tarski(B_170, C_171) | v1_xboole_0(A_169) | ~r1_orders_2(k2_yellow_1(A_169), B_170, C_171) | ~m1_subset_1(C_171, A_169) | ~m1_subset_1(B_170, A_169) | v2_struct_0(k2_yellow_1(A_169)))), inference(resolution, [status(thm)], [c_386, c_61])).
% 2.94/1.51  tff(c_564, plain, (![C_205, B_206]: (r1_tarski(C_205, k10_lattice3(k2_yellow_1('#skF_2'), B_206, C_205)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_206, C_205), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_205, '#skF_2') | ~m1_subset_1(B_206, '#skF_2'))), inference(resolution, [status(thm)], [c_561, c_390])).
% 2.94/1.51  tff(c_573, plain, (![C_205, B_206]: (r1_tarski(C_205, k10_lattice3(k2_yellow_1('#skF_2'), B_206, C_205)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_206, C_205), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_205, '#skF_2') | ~m1_subset_1(B_206, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_564])).
% 2.94/1.51  tff(c_587, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_573])).
% 2.94/1.51  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.51  tff(c_590, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_587, c_8])).
% 2.94/1.51  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_590])).
% 2.94/1.51  tff(c_597, plain, (![C_209, B_210]: (r1_tarski(C_209, k10_lattice3(k2_yellow_1('#skF_2'), B_210, C_209)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_210, C_209), '#skF_2') | ~m1_subset_1(C_209, '#skF_2') | ~m1_subset_1(B_210, '#skF_2'))), inference(splitRight, [status(thm)], [c_573])).
% 2.94/1.51  tff(c_141, plain, (![A_119, B_120, C_121]: (k13_lattice3(A_119, B_120, C_121)=k10_lattice3(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v1_lattice3(A_119) | ~v5_orders_2(A_119))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.94/1.51  tff(c_148, plain, (![A_69, B_120, C_121]: (k13_lattice3(k2_yellow_1(A_69), B_120, C_121)=k10_lattice3(k2_yellow_1(A_69), B_120, C_121) | ~m1_subset_1(C_121, A_69) | ~m1_subset_1(B_120, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v1_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_141])).
% 2.94/1.51  tff(c_153, plain, (![A_122, B_123, C_124]: (k13_lattice3(k2_yellow_1(A_122), B_123, C_124)=k10_lattice3(k2_yellow_1(A_122), B_123, C_124) | ~m1_subset_1(C_124, A_122) | ~m1_subset_1(B_123, A_122) | ~v1_lattice3(k2_yellow_1(A_122)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_148])).
% 2.94/1.51  tff(c_157, plain, (![B_125, C_126]: (k13_lattice3(k2_yellow_1('#skF_2'), B_125, C_126)=k10_lattice3(k2_yellow_1('#skF_2'), B_125, C_126) | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_125, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_153])).
% 2.94/1.51  tff(c_100, plain, (![A_98, B_99, C_100]: (m1_subset_1(k13_lattice3(A_98, B_99, C_100), u1_struct_0(A_98)) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v1_lattice3(A_98) | ~v5_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.51  tff(c_103, plain, (![A_69, B_99, C_100]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_69), B_99, C_100), A_69) | ~m1_subset_1(C_100, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v1_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_100])).
% 2.94/1.51  tff(c_105, plain, (![A_69, B_99, C_100]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_69), B_99, C_100), A_69) | ~m1_subset_1(C_100, A_69) | ~m1_subset_1(B_99, A_69) | ~v1_lattice3(k2_yellow_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_42, c_103])).
% 2.94/1.51  tff(c_163, plain, (![B_125, C_126]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_125, C_126), '#skF_2') | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_125, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_125, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_105])).
% 2.94/1.51  tff(c_172, plain, (![B_125, C_126]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_125, C_126), '#skF_2') | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_125, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_163])).
% 2.94/1.51  tff(c_156, plain, (![B_123, C_124]: (k13_lattice3(k2_yellow_1('#skF_2'), B_123, C_124)=k10_lattice3(k2_yellow_1('#skF_2'), B_123, C_124) | ~m1_subset_1(C_124, '#skF_2') | ~m1_subset_1(B_123, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_153])).
% 2.94/1.51  tff(c_252, plain, (![A_137, C_138, B_139]: (r1_orders_2(A_137, C_138, k13_lattice3(A_137, B_139, C_138)) | ~m1_subset_1(k13_lattice3(A_137, B_139, C_138), u1_struct_0(A_137)) | ~m1_subset_1(C_138, u1_struct_0(A_137)) | ~m1_subset_1(B_139, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v1_lattice3(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.94/1.51  tff(c_268, plain, (![A_140, C_141, B_142]: (r1_orders_2(A_140, C_141, k13_lattice3(A_140, B_142, C_141)) | ~m1_subset_1(C_141, u1_struct_0(A_140)) | ~m1_subset_1(B_142, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v1_lattice3(A_140) | ~v5_orders_2(A_140))), inference(resolution, [status(thm)], [c_10, c_252])).
% 2.94/1.51  tff(c_275, plain, (![C_124, B_123]: (r1_orders_2(k2_yellow_1('#skF_2'), C_124, k10_lattice3(k2_yellow_1('#skF_2'), B_123, C_124)) | ~m1_subset_1(C_124, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_123, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_124, '#skF_2') | ~m1_subset_1(B_123, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_268])).
% 2.94/1.51  tff(c_281, plain, (![C_143, B_144]: (r1_orders_2(k2_yellow_1('#skF_2'), C_143, k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_143)) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_32, c_42, c_42, c_275])).
% 2.94/1.51  tff(c_106, plain, (![A_101, B_102, C_103]: (r3_orders_2(A_101, B_102, C_103) | ~r1_orders_2(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.94/1.51  tff(c_110, plain, (![A_69, B_102, C_103]: (r3_orders_2(k2_yellow_1(A_69), B_102, C_103) | ~r1_orders_2(k2_yellow_1(A_69), B_102, C_103) | ~m1_subset_1(C_103, A_69) | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v3_orders_2(k2_yellow_1(A_69)) | v2_struct_0(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_106])).
% 2.94/1.51  tff(c_119, plain, (![A_107, B_108, C_109]: (r3_orders_2(k2_yellow_1(A_107), B_108, C_109) | ~r1_orders_2(k2_yellow_1(A_107), B_108, C_109) | ~m1_subset_1(C_109, A_107) | ~m1_subset_1(B_108, A_107) | v2_struct_0(k2_yellow_1(A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_42, c_110])).
% 2.94/1.51  tff(c_123, plain, (![B_108, C_109, A_107]: (r1_tarski(B_108, C_109) | v1_xboole_0(A_107) | ~r1_orders_2(k2_yellow_1(A_107), B_108, C_109) | ~m1_subset_1(C_109, A_107) | ~m1_subset_1(B_108, A_107) | v2_struct_0(k2_yellow_1(A_107)))), inference(resolution, [status(thm)], [c_119, c_61])).
% 2.94/1.51  tff(c_284, plain, (![C_143, B_144]: (r1_tarski(C_143, k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_143)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_143), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(resolution, [status(thm)], [c_281, c_123])).
% 2.94/1.51  tff(c_293, plain, (![C_143, B_144]: (r1_tarski(C_143, k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_143)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_144, C_143), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_143, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_284])).
% 2.94/1.51  tff(c_317, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_293])).
% 2.94/1.51  tff(c_320, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_317, c_8])).
% 2.94/1.51  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_320])).
% 2.94/1.51  tff(c_339, plain, (![C_152, B_153]: (r1_tarski(C_152, k10_lattice3(k2_yellow_1('#skF_2'), B_153, C_152)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_153, C_152), '#skF_2') | ~m1_subset_1(C_152, '#skF_2') | ~m1_subset_1(B_153, '#skF_2'))), inference(splitRight, [status(thm)], [c_293])).
% 2.94/1.51  tff(c_177, plain, (![A_129, C_130, B_131]: (k10_lattice3(A_129, C_130, B_131)=k10_lattice3(A_129, B_131, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_129)) | ~m1_subset_1(B_131, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v1_lattice3(A_129) | ~v5_orders_2(A_129))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.51  tff(c_184, plain, (![A_69, C_130, B_131]: (k10_lattice3(k2_yellow_1(A_69), C_130, B_131)=k10_lattice3(k2_yellow_1(A_69), B_131, C_130) | ~m1_subset_1(C_130, A_69) | ~m1_subset_1(B_131, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v1_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_177])).
% 2.94/1.51  tff(c_189, plain, (![A_132, C_133, B_134]: (k10_lattice3(k2_yellow_1(A_132), C_133, B_134)=k10_lattice3(k2_yellow_1(A_132), B_134, C_133) | ~m1_subset_1(C_133, A_132) | ~m1_subset_1(B_134, A_132) | ~v1_lattice3(k2_yellow_1(A_132)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_184])).
% 2.94/1.51  tff(c_193, plain, (![C_135, B_136]: (k10_lattice3(k2_yellow_1('#skF_2'), C_135, B_136)=k10_lattice3(k2_yellow_1('#skF_2'), B_136, C_135) | ~m1_subset_1(C_135, '#skF_2') | ~m1_subset_1(B_136, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_189])).
% 2.94/1.51  tff(c_88, plain, (![A_89, C_90, B_91]: (r1_tarski(k2_xboole_0(A_89, C_90), B_91) | ~r1_tarski(C_90, B_91) | ~r1_tarski(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.51  tff(c_50, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.94/1.51  tff(c_92, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_50])).
% 2.94/1.51  tff(c_93, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_92])).
% 2.94/1.51  tff(c_214, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_193, c_93])).
% 2.94/1.51  tff(c_241, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_214])).
% 2.94/1.51  tff(c_342, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_339, c_241])).
% 2.94/1.51  tff(c_351, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_342])).
% 2.94/1.51  tff(c_354, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_172, c_351])).
% 2.94/1.51  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_354])).
% 2.94/1.51  tff(c_359, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_92])).
% 2.94/1.51  tff(c_600, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_597, c_359])).
% 2.94/1.51  tff(c_609, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_600])).
% 2.94/1.51  tff(c_618, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_434, c_609])).
% 2.94/1.51  tff(c_626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_618])).
% 2.94/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.51  
% 2.94/1.51  Inference rules
% 2.94/1.51  ----------------------
% 2.94/1.51  #Ref     : 0
% 2.94/1.51  #Sup     : 118
% 2.94/1.51  #Fact    : 0
% 2.94/1.51  #Define  : 0
% 2.94/1.51  #Split   : 3
% 2.94/1.51  #Chain   : 0
% 2.94/1.51  #Close   : 0
% 2.94/1.51  
% 2.94/1.51  Ordering : KBO
% 2.94/1.51  
% 2.94/1.51  Simplification rules
% 2.94/1.51  ----------------------
% 2.94/1.51  #Subsume      : 20
% 2.94/1.51  #Demod        : 149
% 2.94/1.51  #Tautology    : 32
% 2.94/1.51  #SimpNegUnit  : 5
% 2.94/1.51  #BackRed      : 0
% 2.94/1.51  
% 2.94/1.51  #Partial instantiations: 0
% 2.94/1.51  #Strategies tried      : 1
% 2.94/1.51  
% 2.94/1.51  Timing (in seconds)
% 2.94/1.51  ----------------------
% 2.94/1.51  Preprocessing        : 0.34
% 2.94/1.51  Parsing              : 0.17
% 2.94/1.51  CNF conversion       : 0.03
% 2.94/1.51  Main loop            : 0.32
% 2.94/1.51  Inferencing          : 0.12
% 2.94/1.51  Reduction            : 0.10
% 2.94/1.51  Demodulation         : 0.07
% 2.94/1.51  BG Simplification    : 0.02
% 2.94/1.51  Subsumption          : 0.05
% 2.94/1.51  Abstraction          : 0.02
% 2.94/1.51  MUC search           : 0.00
% 2.94/1.51  Cooper               : 0.00
% 2.94/1.51  Total                : 0.71
% 2.94/1.51  Index Insertion      : 0.00
% 2.94/1.51  Index Deletion       : 0.00
% 2.94/1.51  Index Matching       : 0.00
% 2.94/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
