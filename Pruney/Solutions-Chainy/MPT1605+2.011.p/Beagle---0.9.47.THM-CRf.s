%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 112 expanded)
%              Number of leaves         :   41 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 ( 257 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_119,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_89,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_38,plain,(
    ! [A_35] : l1_orders_2(k2_yellow_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_57] :
      ( k1_yellow_0(A_57,k1_xboole_0) = k3_yellow_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_102,plain,(
    ! [A_35] : k1_yellow_0(k2_yellow_1(A_35),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_35)) ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_48,plain,(
    ! [A_37] : u1_struct_0(k2_yellow_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_113,plain,(
    ! [A_60,B_61] :
      ( r2_lattice3(A_60,k1_xboole_0,B_61)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_orders_2(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_116,plain,(
    ! [A_37,B_61] :
      ( r2_lattice3(k2_yellow_1(A_37),k1_xboole_0,B_61)
      | ~ m1_subset_1(B_61,A_37)
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_113])).

tff(c_118,plain,(
    ! [A_37,B_61] :
      ( r2_lattice3(k2_yellow_1(A_37),k1_xboole_0,B_61)
      | ~ m1_subset_1(B_61,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_46,plain,(
    ! [A_36] : v5_orders_2(k2_yellow_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_218,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1('#skF_1'(A_114,B_115,C_116),u1_struct_0(A_114))
      | k1_yellow_0(A_114,C_116) = B_115
      | ~ r2_lattice3(A_114,C_116,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_229,plain,(
    ! [A_37,B_115,C_116] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_115,C_116),A_37)
      | k1_yellow_0(k2_yellow_1(A_37),C_116) = B_115
      | ~ r2_lattice3(k2_yellow_1(A_37),C_116,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37))
      | ~ v5_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_218])).

tff(c_234,plain,(
    ! [A_37,B_115,C_116] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_115,C_116),A_37)
      | k1_yellow_0(k2_yellow_1(A_37),C_116) = B_115
      | ~ r2_lattice3(k2_yellow_1(A_37),C_116,B_115)
      | ~ m1_subset_1(B_115,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_48,c_229])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_36] : v3_orders_2(k2_yellow_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    ! [A_38,B_42,C_44] :
      ( r3_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(k2_yellow_1(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    ! [A_38,B_42,C_44] :
      ( r3_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_52])).

tff(c_192,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_orders_2(A_99,B_100,C_101)
      | ~ r3_orders_2(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,(
    ! [A_38,B_42,C_44] :
      ( r1_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(k2_yellow_1(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | ~ l1_orders_2(k2_yellow_1(A_38))
      | ~ v3_orders_2(k2_yellow_1(A_38))
      | v2_struct_0(k2_yellow_1(A_38))
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_62,c_192])).

tff(c_202,plain,(
    ! [A_38,B_42,C_44] :
      ( r1_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | v2_struct_0(k2_yellow_1(A_38))
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_48,c_48,c_196])).

tff(c_235,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ r1_orders_2(A_117,B_118,'#skF_1'(A_117,B_118,C_119))
      | k1_yellow_0(A_117,C_119) = B_118
      | ~ r2_lattice3(A_117,C_119,B_118)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v5_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_239,plain,(
    ! [A_38,C_119,B_42] :
      ( k1_yellow_0(k2_yellow_1(A_38),C_119) = B_42
      | ~ r2_lattice3(k2_yellow_1(A_38),C_119,B_42)
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | ~ l1_orders_2(k2_yellow_1(A_38))
      | ~ v5_orders_2(k2_yellow_1(A_38))
      | v2_struct_0(k2_yellow_1(A_38))
      | ~ r1_tarski(B_42,'#skF_1'(k2_yellow_1(A_38),B_42,C_119))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_38),B_42,C_119),A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_202,c_235])).

tff(c_389,plain,(
    ! [A_182,C_183,B_184] :
      ( k1_yellow_0(k2_yellow_1(A_182),C_183) = B_184
      | ~ r2_lattice3(k2_yellow_1(A_182),C_183,B_184)
      | v2_struct_0(k2_yellow_1(A_182))
      | ~ r1_tarski(B_184,'#skF_1'(k2_yellow_1(A_182),B_184,C_183))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_182),B_184,C_183),A_182)
      | ~ m1_subset_1(B_184,A_182)
      | v1_xboole_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_48,c_239])).

tff(c_394,plain,(
    ! [A_185,C_186] :
      ( k1_yellow_0(k2_yellow_1(A_185),C_186) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_185),C_186,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_185))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_185),k1_xboole_0,C_186),A_185)
      | ~ m1_subset_1(k1_xboole_0,A_185)
      | v1_xboole_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_2,c_389])).

tff(c_421,plain,(
    ! [A_191,C_192] :
      ( v2_struct_0(k2_yellow_1(A_191))
      | v1_xboole_0(A_191)
      | k1_yellow_0(k2_yellow_1(A_191),C_192) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_191),C_192,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_191) ) ),
    inference(resolution,[status(thm)],[c_234,c_394])).

tff(c_425,plain,(
    ! [A_37] :
      ( v2_struct_0(k2_yellow_1(A_37))
      | v1_xboole_0(A_37)
      | k1_yellow_0(k2_yellow_1(A_37),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_37) ) ),
    inference(resolution,[status(thm)],[c_118,c_421])).

tff(c_428,plain,(
    ! [A_193] :
      ( v2_struct_0(k2_yellow_1(A_193))
      | v1_xboole_0(A_193)
      | k3_yellow_0(k2_yellow_1(A_193)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_425])).

tff(c_94,plain,(
    ! [A_56] :
      ( v1_xboole_0(u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | ~ v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_37] :
      ( v1_xboole_0(A_37)
      | ~ l1_struct_0(k2_yellow_1(A_37))
      | ~ v2_struct_0(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_94])).

tff(c_433,plain,(
    ! [A_194] :
      ( ~ l1_struct_0(k2_yellow_1(A_194))
      | v1_xboole_0(A_194)
      | k3_yellow_0(k2_yellow_1(A_194)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_194) ) ),
    inference(resolution,[status(thm)],[c_428,c_97])).

tff(c_436,plain,(
    ! [A_194] :
      ( v1_xboole_0(A_194)
      | k3_yellow_0(k2_yellow_1(A_194)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_194)
      | ~ l1_orders_2(k2_yellow_1(A_194)) ) ),
    inference(resolution,[status(thm)],[c_8,c_433])).

tff(c_456,plain,(
    ! [A_199] :
      ( v1_xboole_0(A_199)
      | k3_yellow_0(k2_yellow_1(A_199)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_436])).

tff(c_56,plain,(
    k3_yellow_0(k2_yellow_1('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_467,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_56])).

tff(c_474,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_467])).

tff(c_476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_474])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.14/1.50  
% 3.14/1.50  %Foreground sorts:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Background operators:
% 3.14/1.50  
% 3.14/1.50  
% 3.14/1.50  %Foreground operators:
% 3.14/1.50  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.14/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.50  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.14/1.50  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.14/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.50  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.50  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.14/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.50  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.14/1.50  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.14/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.50  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.14/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.50  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.14/1.50  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.14/1.50  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.14/1.50  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.14/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.50  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.50  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.14/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.50  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.14/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.50  
% 3.14/1.51  tff(f_140, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.14/1.51  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.14/1.51  tff(f_107, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.14/1.51  tff(f_41, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.14/1.51  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.14/1.51  tff(f_119, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.14/1.51  tff(f_103, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.14/1.51  tff(f_115, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.14/1.51  tff(f_94, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.14/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.14/1.51  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.14/1.51  tff(f_56, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.14/1.51  tff(f_37, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.14/1.51  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.51  tff(c_58, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.51  tff(c_89, plain, (![A_54, B_55]: (m1_subset_1(A_54, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.51  tff(c_93, plain, (m1_subset_1(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_58, c_89])).
% 3.14/1.51  tff(c_38, plain, (![A_35]: (l1_orders_2(k2_yellow_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.14/1.51  tff(c_8, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.14/1.51  tff(c_98, plain, (![A_57]: (k1_yellow_0(A_57, k1_xboole_0)=k3_yellow_0(A_57) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.14/1.51  tff(c_102, plain, (![A_35]: (k1_yellow_0(k2_yellow_1(A_35), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_35)))), inference(resolution, [status(thm)], [c_38, c_98])).
% 3.14/1.51  tff(c_48, plain, (![A_37]: (u1_struct_0(k2_yellow_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.14/1.51  tff(c_113, plain, (![A_60, B_61]: (r2_lattice3(A_60, k1_xboole_0, B_61) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_orders_2(A_60))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.14/1.51  tff(c_116, plain, (![A_37, B_61]: (r2_lattice3(k2_yellow_1(A_37), k1_xboole_0, B_61) | ~m1_subset_1(B_61, A_37) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_113])).
% 3.14/1.51  tff(c_118, plain, (![A_37, B_61]: (r2_lattice3(k2_yellow_1(A_37), k1_xboole_0, B_61) | ~m1_subset_1(B_61, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 3.14/1.51  tff(c_46, plain, (![A_36]: (v5_orders_2(k2_yellow_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.14/1.51  tff(c_218, plain, (![A_114, B_115, C_116]: (m1_subset_1('#skF_1'(A_114, B_115, C_116), u1_struct_0(A_114)) | k1_yellow_0(A_114, C_116)=B_115 | ~r2_lattice3(A_114, C_116, B_115) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.51  tff(c_229, plain, (![A_37, B_115, C_116]: (m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_115, C_116), A_37) | k1_yellow_0(k2_yellow_1(A_37), C_116)=B_115 | ~r2_lattice3(k2_yellow_1(A_37), C_116, B_115) | ~m1_subset_1(B_115, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v5_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_218])).
% 3.14/1.51  tff(c_234, plain, (![A_37, B_115, C_116]: (m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_115, C_116), A_37) | k1_yellow_0(k2_yellow_1(A_37), C_116)=B_115 | ~r2_lattice3(k2_yellow_1(A_37), C_116, B_115) | ~m1_subset_1(B_115, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_48, c_229])).
% 3.14/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.51  tff(c_42, plain, (![A_36]: (v3_orders_2(k2_yellow_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.14/1.51  tff(c_52, plain, (![A_38, B_42, C_44]: (r3_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, u1_struct_0(k2_yellow_1(A_38))) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.14/1.51  tff(c_62, plain, (![A_38, B_42, C_44]: (r3_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_52])).
% 3.14/1.51  tff(c_192, plain, (![A_99, B_100, C_101]: (r1_orders_2(A_99, B_100, C_101) | ~r3_orders_2(A_99, B_100, C_101) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.14/1.51  tff(c_196, plain, (![A_38, B_42, C_44]: (r1_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~m1_subset_1(C_44, u1_struct_0(k2_yellow_1(A_38))) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | ~l1_orders_2(k2_yellow_1(A_38)) | ~v3_orders_2(k2_yellow_1(A_38)) | v2_struct_0(k2_yellow_1(A_38)) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_62, c_192])).
% 3.14/1.51  tff(c_202, plain, (![A_38, B_42, C_44]: (r1_orders_2(k2_yellow_1(A_38), B_42, C_44) | v2_struct_0(k2_yellow_1(A_38)) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_48, c_48, c_196])).
% 3.14/1.51  tff(c_235, plain, (![A_117, B_118, C_119]: (~r1_orders_2(A_117, B_118, '#skF_1'(A_117, B_118, C_119)) | k1_yellow_0(A_117, C_119)=B_118 | ~r2_lattice3(A_117, C_119, B_118) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_orders_2(A_117) | ~v5_orders_2(A_117))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.51  tff(c_239, plain, (![A_38, C_119, B_42]: (k1_yellow_0(k2_yellow_1(A_38), C_119)=B_42 | ~r2_lattice3(k2_yellow_1(A_38), C_119, B_42) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | ~l1_orders_2(k2_yellow_1(A_38)) | ~v5_orders_2(k2_yellow_1(A_38)) | v2_struct_0(k2_yellow_1(A_38)) | ~r1_tarski(B_42, '#skF_1'(k2_yellow_1(A_38), B_42, C_119)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_38), B_42, C_119), A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_202, c_235])).
% 3.14/1.51  tff(c_389, plain, (![A_182, C_183, B_184]: (k1_yellow_0(k2_yellow_1(A_182), C_183)=B_184 | ~r2_lattice3(k2_yellow_1(A_182), C_183, B_184) | v2_struct_0(k2_yellow_1(A_182)) | ~r1_tarski(B_184, '#skF_1'(k2_yellow_1(A_182), B_184, C_183)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_182), B_184, C_183), A_182) | ~m1_subset_1(B_184, A_182) | v1_xboole_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_48, c_239])).
% 3.14/1.51  tff(c_394, plain, (![A_185, C_186]: (k1_yellow_0(k2_yellow_1(A_185), C_186)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_185), C_186, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_185)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_185), k1_xboole_0, C_186), A_185) | ~m1_subset_1(k1_xboole_0, A_185) | v1_xboole_0(A_185))), inference(resolution, [status(thm)], [c_2, c_389])).
% 3.14/1.51  tff(c_421, plain, (![A_191, C_192]: (v2_struct_0(k2_yellow_1(A_191)) | v1_xboole_0(A_191) | k1_yellow_0(k2_yellow_1(A_191), C_192)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_191), C_192, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_191))), inference(resolution, [status(thm)], [c_234, c_394])).
% 3.14/1.51  tff(c_425, plain, (![A_37]: (v2_struct_0(k2_yellow_1(A_37)) | v1_xboole_0(A_37) | k1_yellow_0(k2_yellow_1(A_37), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_37))), inference(resolution, [status(thm)], [c_118, c_421])).
% 3.14/1.51  tff(c_428, plain, (![A_193]: (v2_struct_0(k2_yellow_1(A_193)) | v1_xboole_0(A_193) | k3_yellow_0(k2_yellow_1(A_193))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_193))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_425])).
% 3.14/1.51  tff(c_94, plain, (![A_56]: (v1_xboole_0(u1_struct_0(A_56)) | ~l1_struct_0(A_56) | ~v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.51  tff(c_97, plain, (![A_37]: (v1_xboole_0(A_37) | ~l1_struct_0(k2_yellow_1(A_37)) | ~v2_struct_0(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_94])).
% 3.14/1.51  tff(c_433, plain, (![A_194]: (~l1_struct_0(k2_yellow_1(A_194)) | v1_xboole_0(A_194) | k3_yellow_0(k2_yellow_1(A_194))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_194))), inference(resolution, [status(thm)], [c_428, c_97])).
% 3.14/1.51  tff(c_436, plain, (![A_194]: (v1_xboole_0(A_194) | k3_yellow_0(k2_yellow_1(A_194))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_194) | ~l1_orders_2(k2_yellow_1(A_194)))), inference(resolution, [status(thm)], [c_8, c_433])).
% 3.14/1.51  tff(c_456, plain, (![A_199]: (v1_xboole_0(A_199) | k3_yellow_0(k2_yellow_1(A_199))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_199))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_436])).
% 3.14/1.51  tff(c_56, plain, (k3_yellow_0(k2_yellow_1('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.51  tff(c_467, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_456, c_56])).
% 3.14/1.51  tff(c_474, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_467])).
% 3.14/1.51  tff(c_476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_474])).
% 3.14/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  Inference rules
% 3.14/1.51  ----------------------
% 3.14/1.51  #Ref     : 0
% 3.14/1.52  #Sup     : 75
% 3.14/1.52  #Fact    : 0
% 3.14/1.52  #Define  : 0
% 3.14/1.52  #Split   : 0
% 3.14/1.52  #Chain   : 0
% 3.14/1.52  #Close   : 0
% 3.14/1.52  
% 3.14/1.52  Ordering : KBO
% 3.14/1.52  
% 3.14/1.52  Simplification rules
% 3.14/1.52  ----------------------
% 3.14/1.52  #Subsume      : 14
% 3.14/1.52  #Demod        : 120
% 3.14/1.52  #Tautology    : 15
% 3.14/1.52  #SimpNegUnit  : 1
% 3.14/1.52  #BackRed      : 0
% 3.14/1.52  
% 3.14/1.52  #Partial instantiations: 0
% 3.14/1.52  #Strategies tried      : 1
% 3.14/1.52  
% 3.14/1.52  Timing (in seconds)
% 3.14/1.52  ----------------------
% 3.14/1.52  Preprocessing        : 0.36
% 3.14/1.52  Parsing              : 0.19
% 3.14/1.52  CNF conversion       : 0.02
% 3.14/1.52  Main loop            : 0.33
% 3.14/1.52  Inferencing          : 0.14
% 3.14/1.52  Reduction            : 0.09
% 3.14/1.52  Demodulation         : 0.07
% 3.14/1.52  BG Simplification    : 0.02
% 3.14/1.52  Subsumption          : 0.06
% 3.14/1.52  Abstraction          : 0.02
% 3.14/1.52  MUC search           : 0.00
% 3.14/1.52  Cooper               : 0.00
% 3.14/1.52  Total                : 0.72
% 3.14/1.52  Index Insertion      : 0.00
% 3.14/1.52  Index Deletion       : 0.00
% 3.14/1.52  Index Matching       : 0.00
% 3.14/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
