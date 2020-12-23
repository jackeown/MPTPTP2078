%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 122 expanded)
%              Number of leaves         :   43 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 ( 272 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_123,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_struct_0)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_60,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_91,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(A_55,B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_40,plain,(
    ! [A_36] : l1_orders_2(k2_yellow_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_120,plain,(
    ! [A_61] :
      ( k1_yellow_0(A_61,k1_xboole_0) = k3_yellow_0(A_61)
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_124,plain,(
    ! [A_36] : k1_yellow_0(k2_yellow_1(A_36),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_36)) ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_50,plain,(
    ! [A_38] : u1_struct_0(k2_yellow_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_125,plain,(
    ! [A_62,B_63] :
      ( r2_lattice3(A_62,k1_xboole_0,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_128,plain,(
    ! [A_38,B_63] :
      ( r2_lattice3(k2_yellow_1(A_38),k1_xboole_0,B_63)
      | ~ m1_subset_1(B_63,A_38)
      | ~ l1_orders_2(k2_yellow_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_125])).

tff(c_130,plain,(
    ! [A_38,B_63] :
      ( r2_lattice3(k2_yellow_1(A_38),k1_xboole_0,B_63)
      | ~ m1_subset_1(B_63,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_128])).

tff(c_48,plain,(
    ! [A_37] : v5_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_240,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1('#skF_1'(A_118,B_119,C_120),u1_struct_0(A_118))
      | k1_yellow_0(A_118,C_120) = B_119
      | ~ r2_lattice3(A_118,C_120,B_119)
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_251,plain,(
    ! [A_38,B_119,C_120] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_38),B_119,C_120),A_38)
      | k1_yellow_0(k2_yellow_1(A_38),C_120) = B_119
      | ~ r2_lattice3(k2_yellow_1(A_38),C_120,B_119)
      | ~ m1_subset_1(B_119,u1_struct_0(k2_yellow_1(A_38)))
      | ~ l1_orders_2(k2_yellow_1(A_38))
      | ~ v5_orders_2(k2_yellow_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_240])).

tff(c_256,plain,(
    ! [A_38,B_119,C_120] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_38),B_119,C_120),A_38)
      | k1_yellow_0(k2_yellow_1(A_38),C_120) = B_119
      | ~ r2_lattice3(k2_yellow_1(A_38),C_120,B_119)
      | ~ m1_subset_1(B_119,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_50,c_251])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_37] : v3_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    ! [A_39,B_43,C_45] :
      ( r3_orders_2(k2_yellow_1(A_39),B_43,C_45)
      | ~ r1_tarski(B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(k2_yellow_1(A_39)))
      | ~ m1_subset_1(B_43,u1_struct_0(k2_yellow_1(A_39)))
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_64,plain,(
    ! [A_39,B_43,C_45] :
      ( r3_orders_2(k2_yellow_1(A_39),B_43,C_45)
      | ~ r1_tarski(B_43,C_45)
      | ~ m1_subset_1(C_45,A_39)
      | ~ m1_subset_1(B_43,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_54])).

tff(c_169,plain,(
    ! [A_82,B_83,C_84] :
      ( r1_orders_2(A_82,B_83,C_84)
      | ~ r3_orders_2(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_171,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(k2_yellow_1(A_39),B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(k2_yellow_1(A_39)))
      | ~ m1_subset_1(B_43,u1_struct_0(k2_yellow_1(A_39)))
      | ~ l1_orders_2(k2_yellow_1(A_39))
      | ~ v3_orders_2(k2_yellow_1(A_39))
      | v2_struct_0(k2_yellow_1(A_39))
      | ~ r1_tarski(B_43,C_45)
      | ~ m1_subset_1(C_45,A_39)
      | ~ m1_subset_1(B_43,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_64,c_169])).

tff(c_174,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(k2_yellow_1(A_39),B_43,C_45)
      | v2_struct_0(k2_yellow_1(A_39))
      | ~ r1_tarski(B_43,C_45)
      | ~ m1_subset_1(C_45,A_39)
      | ~ m1_subset_1(B_43,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_50,c_50,c_171])).

tff(c_272,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_orders_2(A_124,B_125,'#skF_1'(A_124,B_125,C_126))
      | k1_yellow_0(A_124,C_126) = B_125
      | ~ r2_lattice3(A_124,C_126,B_125)
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_276,plain,(
    ! [A_39,C_126,B_43] :
      ( k1_yellow_0(k2_yellow_1(A_39),C_126) = B_43
      | ~ r2_lattice3(k2_yellow_1(A_39),C_126,B_43)
      | ~ m1_subset_1(B_43,u1_struct_0(k2_yellow_1(A_39)))
      | ~ l1_orders_2(k2_yellow_1(A_39))
      | ~ v5_orders_2(k2_yellow_1(A_39))
      | v2_struct_0(k2_yellow_1(A_39))
      | ~ r1_tarski(B_43,'#skF_1'(k2_yellow_1(A_39),B_43,C_126))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_39),B_43,C_126),A_39)
      | ~ m1_subset_1(B_43,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_174,c_272])).

tff(c_411,plain,(
    ! [A_186,C_187,B_188] :
      ( k1_yellow_0(k2_yellow_1(A_186),C_187) = B_188
      | ~ r2_lattice3(k2_yellow_1(A_186),C_187,B_188)
      | v2_struct_0(k2_yellow_1(A_186))
      | ~ r1_tarski(B_188,'#skF_1'(k2_yellow_1(A_186),B_188,C_187))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_186),B_188,C_187),A_186)
      | ~ m1_subset_1(B_188,A_186)
      | v1_xboole_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_50,c_276])).

tff(c_416,plain,(
    ! [A_189,C_190] :
      ( k1_yellow_0(k2_yellow_1(A_189),C_190) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_189),C_190,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_189))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_189),k1_xboole_0,C_190),A_189)
      | ~ m1_subset_1(k1_xboole_0,A_189)
      | v1_xboole_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_2,c_411])).

tff(c_427,plain,(
    ! [A_191,C_192] :
      ( v2_struct_0(k2_yellow_1(A_191))
      | v1_xboole_0(A_191)
      | k1_yellow_0(k2_yellow_1(A_191),C_192) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_191),C_192,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_191) ) ),
    inference(resolution,[status(thm)],[c_256,c_416])).

tff(c_431,plain,(
    ! [A_38] :
      ( v2_struct_0(k2_yellow_1(A_38))
      | v1_xboole_0(A_38)
      | k1_yellow_0(k2_yellow_1(A_38),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_38) ) ),
    inference(resolution,[status(thm)],[c_130,c_427])).

tff(c_450,plain,(
    ! [A_197] :
      ( v2_struct_0(k2_yellow_1(A_197))
      | v1_xboole_0(A_197)
      | k3_yellow_0(k2_yellow_1(A_197)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_431])).

tff(c_96,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_orders_2(A_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_105,plain,(
    ! [A_36] : u1_struct_0(k2_yellow_1(A_36)) = k2_struct_0(k2_yellow_1(A_36)) ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_108,plain,(
    ! [A_60] : k2_struct_0(k2_yellow_1(A_60)) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_105])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_xboole_0(k2_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | ~ v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [A_60] :
      ( v1_xboole_0(A_60)
      | ~ l1_struct_0(k2_yellow_1(A_60))
      | ~ v2_struct_0(k2_yellow_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_455,plain,(
    ! [A_198] :
      ( ~ l1_struct_0(k2_yellow_1(A_198))
      | v1_xboole_0(A_198)
      | k3_yellow_0(k2_yellow_1(A_198)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_198) ) ),
    inference(resolution,[status(thm)],[c_450,c_114])).

tff(c_458,plain,(
    ! [A_198] :
      ( v1_xboole_0(A_198)
      | k3_yellow_0(k2_yellow_1(A_198)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_198)
      | ~ l1_orders_2(k2_yellow_1(A_198)) ) ),
    inference(resolution,[status(thm)],[c_10,c_455])).

tff(c_462,plain,(
    ! [A_199] :
      ( v1_xboole_0(A_199)
      | k3_yellow_0(k2_yellow_1(A_199)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_458])).

tff(c_58,plain,(
    k3_yellow_0(k2_yellow_1('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_473,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_58])).

tff(c_480,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_473])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.51  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k2_struct_0 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
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
% 3.14/1.51  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.51  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.51  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.14/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.51  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.14/1.51  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.51  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.14/1.51  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.14/1.51  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.14/1.51  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.14/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.51  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.14/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.14/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.51  
% 3.26/1.53  tff(f_144, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.26/1.53  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.26/1.53  tff(f_111, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.26/1.53  tff(f_45, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.26/1.53  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.26/1.53  tff(f_123, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.26/1.53  tff(f_107, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.26/1.53  tff(f_119, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.26/1.53  tff(f_98, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.26/1.53  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.53  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.26/1.53  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.26/1.53  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.26/1.53  tff(f_41, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_struct_0)).
% 3.26/1.53  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.53  tff(c_60, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.53  tff(c_91, plain, (![A_55, B_56]: (m1_subset_1(A_55, B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.53  tff(c_95, plain, (m1_subset_1(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.26/1.53  tff(c_40, plain, (![A_36]: (l1_orders_2(k2_yellow_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.53  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.53  tff(c_120, plain, (![A_61]: (k1_yellow_0(A_61, k1_xboole_0)=k3_yellow_0(A_61) | ~l1_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.26/1.53  tff(c_124, plain, (![A_36]: (k1_yellow_0(k2_yellow_1(A_36), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_36)))), inference(resolution, [status(thm)], [c_40, c_120])).
% 3.26/1.53  tff(c_50, plain, (![A_38]: (u1_struct_0(k2_yellow_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.26/1.53  tff(c_125, plain, (![A_62, B_63]: (r2_lattice3(A_62, k1_xboole_0, B_63) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_orders_2(A_62))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.26/1.53  tff(c_128, plain, (![A_38, B_63]: (r2_lattice3(k2_yellow_1(A_38), k1_xboole_0, B_63) | ~m1_subset_1(B_63, A_38) | ~l1_orders_2(k2_yellow_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_125])).
% 3.26/1.53  tff(c_130, plain, (![A_38, B_63]: (r2_lattice3(k2_yellow_1(A_38), k1_xboole_0, B_63) | ~m1_subset_1(B_63, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_128])).
% 3.26/1.53  tff(c_48, plain, (![A_37]: (v5_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.26/1.53  tff(c_240, plain, (![A_118, B_119, C_120]: (m1_subset_1('#skF_1'(A_118, B_119, C_120), u1_struct_0(A_118)) | k1_yellow_0(A_118, C_120)=B_119 | ~r2_lattice3(A_118, C_120, B_119) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.26/1.53  tff(c_251, plain, (![A_38, B_119, C_120]: (m1_subset_1('#skF_1'(k2_yellow_1(A_38), B_119, C_120), A_38) | k1_yellow_0(k2_yellow_1(A_38), C_120)=B_119 | ~r2_lattice3(k2_yellow_1(A_38), C_120, B_119) | ~m1_subset_1(B_119, u1_struct_0(k2_yellow_1(A_38))) | ~l1_orders_2(k2_yellow_1(A_38)) | ~v5_orders_2(k2_yellow_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_240])).
% 3.26/1.53  tff(c_256, plain, (![A_38, B_119, C_120]: (m1_subset_1('#skF_1'(k2_yellow_1(A_38), B_119, C_120), A_38) | k1_yellow_0(k2_yellow_1(A_38), C_120)=B_119 | ~r2_lattice3(k2_yellow_1(A_38), C_120, B_119) | ~m1_subset_1(B_119, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_50, c_251])).
% 3.26/1.53  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.53  tff(c_44, plain, (![A_37]: (v3_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.26/1.53  tff(c_54, plain, (![A_39, B_43, C_45]: (r3_orders_2(k2_yellow_1(A_39), B_43, C_45) | ~r1_tarski(B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(k2_yellow_1(A_39))) | ~m1_subset_1(B_43, u1_struct_0(k2_yellow_1(A_39))) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.26/1.53  tff(c_64, plain, (![A_39, B_43, C_45]: (r3_orders_2(k2_yellow_1(A_39), B_43, C_45) | ~r1_tarski(B_43, C_45) | ~m1_subset_1(C_45, A_39) | ~m1_subset_1(B_43, A_39) | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_54])).
% 3.26/1.53  tff(c_169, plain, (![A_82, B_83, C_84]: (r1_orders_2(A_82, B_83, C_84) | ~r3_orders_2(A_82, B_83, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.26/1.53  tff(c_171, plain, (![A_39, B_43, C_45]: (r1_orders_2(k2_yellow_1(A_39), B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(k2_yellow_1(A_39))) | ~m1_subset_1(B_43, u1_struct_0(k2_yellow_1(A_39))) | ~l1_orders_2(k2_yellow_1(A_39)) | ~v3_orders_2(k2_yellow_1(A_39)) | v2_struct_0(k2_yellow_1(A_39)) | ~r1_tarski(B_43, C_45) | ~m1_subset_1(C_45, A_39) | ~m1_subset_1(B_43, A_39) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_64, c_169])).
% 3.26/1.53  tff(c_174, plain, (![A_39, B_43, C_45]: (r1_orders_2(k2_yellow_1(A_39), B_43, C_45) | v2_struct_0(k2_yellow_1(A_39)) | ~r1_tarski(B_43, C_45) | ~m1_subset_1(C_45, A_39) | ~m1_subset_1(B_43, A_39) | v1_xboole_0(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_50, c_50, c_171])).
% 3.26/1.53  tff(c_272, plain, (![A_124, B_125, C_126]: (~r1_orders_2(A_124, B_125, '#skF_1'(A_124, B_125, C_126)) | k1_yellow_0(A_124, C_126)=B_125 | ~r2_lattice3(A_124, C_126, B_125) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.26/1.53  tff(c_276, plain, (![A_39, C_126, B_43]: (k1_yellow_0(k2_yellow_1(A_39), C_126)=B_43 | ~r2_lattice3(k2_yellow_1(A_39), C_126, B_43) | ~m1_subset_1(B_43, u1_struct_0(k2_yellow_1(A_39))) | ~l1_orders_2(k2_yellow_1(A_39)) | ~v5_orders_2(k2_yellow_1(A_39)) | v2_struct_0(k2_yellow_1(A_39)) | ~r1_tarski(B_43, '#skF_1'(k2_yellow_1(A_39), B_43, C_126)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_39), B_43, C_126), A_39) | ~m1_subset_1(B_43, A_39) | v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_174, c_272])).
% 3.26/1.53  tff(c_411, plain, (![A_186, C_187, B_188]: (k1_yellow_0(k2_yellow_1(A_186), C_187)=B_188 | ~r2_lattice3(k2_yellow_1(A_186), C_187, B_188) | v2_struct_0(k2_yellow_1(A_186)) | ~r1_tarski(B_188, '#skF_1'(k2_yellow_1(A_186), B_188, C_187)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_186), B_188, C_187), A_186) | ~m1_subset_1(B_188, A_186) | v1_xboole_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_50, c_276])).
% 3.26/1.53  tff(c_416, plain, (![A_189, C_190]: (k1_yellow_0(k2_yellow_1(A_189), C_190)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_189), C_190, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_189)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_189), k1_xboole_0, C_190), A_189) | ~m1_subset_1(k1_xboole_0, A_189) | v1_xboole_0(A_189))), inference(resolution, [status(thm)], [c_2, c_411])).
% 3.26/1.53  tff(c_427, plain, (![A_191, C_192]: (v2_struct_0(k2_yellow_1(A_191)) | v1_xboole_0(A_191) | k1_yellow_0(k2_yellow_1(A_191), C_192)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_191), C_192, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_191))), inference(resolution, [status(thm)], [c_256, c_416])).
% 3.26/1.53  tff(c_431, plain, (![A_38]: (v2_struct_0(k2_yellow_1(A_38)) | v1_xboole_0(A_38) | k1_yellow_0(k2_yellow_1(A_38), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_38))), inference(resolution, [status(thm)], [c_130, c_427])).
% 3.26/1.53  tff(c_450, plain, (![A_197]: (v2_struct_0(k2_yellow_1(A_197)) | v1_xboole_0(A_197) | k3_yellow_0(k2_yellow_1(A_197))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_197))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_431])).
% 3.26/1.53  tff(c_96, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.53  tff(c_102, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_orders_2(A_59))), inference(resolution, [status(thm)], [c_10, c_96])).
% 3.26/1.53  tff(c_105, plain, (![A_36]: (u1_struct_0(k2_yellow_1(A_36))=k2_struct_0(k2_yellow_1(A_36)))), inference(resolution, [status(thm)], [c_40, c_102])).
% 3.26/1.53  tff(c_108, plain, (![A_60]: (k2_struct_0(k2_yellow_1(A_60))=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_105])).
% 3.26/1.53  tff(c_8, plain, (![A_5]: (v1_xboole_0(k2_struct_0(A_5)) | ~l1_struct_0(A_5) | ~v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.53  tff(c_114, plain, (![A_60]: (v1_xboole_0(A_60) | ~l1_struct_0(k2_yellow_1(A_60)) | ~v2_struct_0(k2_yellow_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 3.26/1.53  tff(c_455, plain, (![A_198]: (~l1_struct_0(k2_yellow_1(A_198)) | v1_xboole_0(A_198) | k3_yellow_0(k2_yellow_1(A_198))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_198))), inference(resolution, [status(thm)], [c_450, c_114])).
% 3.26/1.53  tff(c_458, plain, (![A_198]: (v1_xboole_0(A_198) | k3_yellow_0(k2_yellow_1(A_198))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_198) | ~l1_orders_2(k2_yellow_1(A_198)))), inference(resolution, [status(thm)], [c_10, c_455])).
% 3.26/1.53  tff(c_462, plain, (![A_199]: (v1_xboole_0(A_199) | k3_yellow_0(k2_yellow_1(A_199))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_199))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_458])).
% 3.26/1.53  tff(c_58, plain, (k3_yellow_0(k2_yellow_1('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.26/1.53  tff(c_473, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_462, c_58])).
% 3.26/1.53  tff(c_480, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_473])).
% 3.26/1.53  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_480])).
% 3.26/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.53  
% 3.26/1.53  Inference rules
% 3.26/1.53  ----------------------
% 3.26/1.53  #Ref     : 0
% 3.26/1.53  #Sup     : 76
% 3.26/1.53  #Fact    : 0
% 3.26/1.53  #Define  : 0
% 3.26/1.53  #Split   : 0
% 3.26/1.53  #Chain   : 0
% 3.26/1.53  #Close   : 0
% 3.26/1.53  
% 3.26/1.53  Ordering : KBO
% 3.26/1.53  
% 3.26/1.53  Simplification rules
% 3.26/1.53  ----------------------
% 3.26/1.53  #Subsume      : 13
% 3.26/1.53  #Demod        : 105
% 3.26/1.53  #Tautology    : 16
% 3.26/1.53  #SimpNegUnit  : 1
% 3.26/1.53  #BackRed      : 0
% 3.26/1.53  
% 3.26/1.53  #Partial instantiations: 0
% 3.26/1.53  #Strategies tried      : 1
% 3.26/1.53  
% 3.26/1.53  Timing (in seconds)
% 3.26/1.53  ----------------------
% 3.26/1.53  Preprocessing        : 0.37
% 3.26/1.53  Parsing              : 0.20
% 3.26/1.53  CNF conversion       : 0.02
% 3.26/1.53  Main loop            : 0.34
% 3.26/1.53  Inferencing          : 0.14
% 3.26/1.53  Reduction            : 0.10
% 3.26/1.53  Demodulation         : 0.07
% 3.26/1.53  BG Simplification    : 0.02
% 3.26/1.53  Subsumption          : 0.05
% 3.26/1.53  Abstraction          : 0.02
% 3.26/1.53  MUC search           : 0.00
% 3.26/1.53  Cooper               : 0.00
% 3.26/1.53  Total                : 0.74
% 3.26/1.53  Index Insertion      : 0.00
% 3.26/1.53  Index Deletion       : 0.00
% 3.26/1.53  Index Matching       : 0.00
% 3.26/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
