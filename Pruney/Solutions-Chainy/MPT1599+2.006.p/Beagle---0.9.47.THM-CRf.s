%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 688 expanded)
%              Number of leaves         :   36 ( 280 expanded)
%              Depth                    :   14
%              Number of atoms          :  350 (2013 expanded)
%              Number of equality atoms :   57 ( 157 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_85,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k12_lattice3(A,B,C)
              <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_104,axiom,(
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
                 => ( v4_orders_2(A)
                   => k11_lattice3(A,k11_lattice3(A,B,C),D) = k11_lattice3(A,B,k11_lattice3(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_lattice3)).

tff(f_149,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32,plain,(
    ! [A_45] : v5_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v2_lattice3(k2_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_24,plain,(
    ! [A_44] : l1_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1896,plain,(
    ! [A_160,C_161,B_162] :
      ( k11_lattice3(A_160,C_161,B_162) = k11_lattice3(A_160,B_162,C_161)
      | ~ m1_subset_1(C_161,u1_struct_0(A_160))
      | ~ m1_subset_1(B_162,u1_struct_0(A_160))
      | ~ l1_orders_2(A_160)
      | ~ v2_lattice3(A_160)
      | ~ v5_orders_2(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1900,plain,(
    ! [B_162] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_162,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1896])).

tff(c_1910,plain,(
    ! [B_163] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_163,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',B_163)
      | ~ m1_subset_1(B_163,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_1900])).

tff(c_1926,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1910])).

tff(c_160,plain,(
    ! [A_81,C_82,B_83] :
      ( k11_lattice3(A_81,C_82,B_83) = k11_lattice3(A_81,B_83,C_82)
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ m1_subset_1(B_83,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | ~ v2_lattice3(A_81)
      | ~ v5_orders_2(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_164,plain,(
    ! [B_83] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_83,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_160])).

tff(c_193,plain,(
    ! [B_85] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_85,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',B_85)
      | ~ m1_subset_1(B_85,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_164])).

tff(c_209,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_193])).

tff(c_63,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(A_64,k3_xboole_0(B_65,C_66))
      | ~ r1_tarski(A_64,C_66)
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_67,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_38])).

tff(c_68,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_210,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_68])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k11_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_215,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_8])).

tff(c_219,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_40,c_215])).

tff(c_166,plain,(
    ! [B_83] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_83,'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_160])).

tff(c_281,plain,(
    ! [B_89] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_89,'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',B_89)
      | ~ m1_subset_1(B_89,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_166])).

tff(c_295,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_219,c_281])).

tff(c_262,plain,(
    ! [A_86,B_87,C_88] :
      ( k12_lattice3(A_86,B_87,C_88) = k11_lattice3(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v2_lattice3(A_86)
      | ~ v5_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_270,plain,(
    ! [B_87] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_87,'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),B_87,'#skF_2')
      | ~ m1_subset_1(B_87,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_262])).

tff(c_332,plain,(
    ! [B_91] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_91,'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),B_91,'#skF_2')
      | ~ m1_subset_1(B_91,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_270])).

tff(c_346,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_219,c_332])).

tff(c_1474,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_346])).

tff(c_28,plain,(
    ! [A_45] : v3_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1220,plain,(
    ! [A_117,B_118,C_119] :
      ( r3_orders_2(A_117,B_118,C_119)
      | k12_lattice3(A_117,B_118,C_119) != B_118
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v2_lattice3(A_117)
      | ~ v5_orders_2(A_117)
      | ~ v3_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1230,plain,(
    ! [B_118] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_118,'#skF_2')
      | k12_lattice3(k2_yellow_1('#skF_1'),B_118,'#skF_2') != B_118
      | ~ m1_subset_1(B_118,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1220])).

tff(c_1279,plain,(
    ! [B_122] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_122,'#skF_2')
      | k12_lattice3(k2_yellow_1('#skF_1'),B_122,'#skF_2') != B_122
      | ~ m1_subset_1(B_122,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_44,c_24,c_1230])).

tff(c_1297,plain,
    ( r3_orders_2(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2')
    | k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') != k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_219,c_1279])).

tff(c_1639,plain,
    ( r3_orders_2(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2')
    | k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) != k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_1297])).

tff(c_1640,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) != k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_351,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_332])).

tff(c_70,plain,(
    ! [A_70,B_71,C_72] :
      ( r3_orders_2(A_70,B_71,B_71)
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [B_71] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_71,B_71)
      | ~ m1_subset_1(B_71,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1'))
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_70])).

tff(c_80,plain,(
    ! [B_71] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_71,B_71)
      | ~ m1_subset_1(B_71,u1_struct_0(k2_yellow_1('#skF_1')))
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_74])).

tff(c_84,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_6,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v2_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_6])).

tff(c_91,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_44,c_87])).

tff(c_98,plain,(
    ! [B_73] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_73,B_73)
      | ~ m1_subset_1(B_73,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_110,plain,(
    r3_orders_2(k2_yellow_1('#skF_1'),'#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_98])).

tff(c_1376,plain,(
    ! [A_123,B_124,C_125] :
      ( k12_lattice3(A_123,B_124,C_125) = B_124
      | ~ r3_orders_2(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v2_lattice3(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v3_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1386,plain,
    ( k12_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ l1_orders_2(k2_yellow_1('#skF_1'))
    | ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ v5_orders_2(k2_yellow_1('#skF_1'))
    | ~ v3_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_110,c_1376])).

tff(c_1403,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_44,c_24,c_42,c_351,c_1386])).

tff(c_30,plain,(
    ! [A_45] : v4_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1479,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k11_lattice3(A_127,k11_lattice3(A_127,B_128,C_129),D_130) = k11_lattice3(A_127,B_128,k11_lattice3(A_127,C_129,D_130))
      | ~ v4_orders_2(A_127)
      | ~ m1_subset_1(D_130,u1_struct_0(A_127))
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v5_orders_2(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1487,plain,(
    ! [B_128,C_129] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),B_128,C_129),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),B_128,k11_lattice3(k2_yellow_1('#skF_1'),C_129,'#skF_3'))
      | ~ v4_orders_2(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_129,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_128,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1479])).

tff(c_1641,plain,(
    ! [B_138,C_139] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),B_138,C_139),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),B_138,k11_lattice3(k2_yellow_1('#skF_1'),C_139,'#skF_3'))
      | ~ m1_subset_1(C_139,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_138,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_30,c_1487])).

tff(c_1680,plain,
    ( k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3')) = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_1641])).

tff(c_1710,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_209,c_209,c_1680])).

tff(c_1712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1640,c_1710])).

tff(c_1713,plain,(
    r3_orders_2(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_36,plain,(
    ! [B_50,C_52,A_46] :
      ( r1_tarski(B_50,C_52)
      | ~ r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1718,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1713,c_36])).

tff(c_1724,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_42,c_1718])).

tff(c_1726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_210,c_1724])).

tff(c_1727,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1929,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1727])).

tff(c_1934,plain,
    ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_8])).

tff(c_1938,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_42,c_40,c_1934])).

tff(c_1834,plain,(
    ! [A_155,B_156,C_157] :
      ( k12_lattice3(A_155,B_156,C_157) = k11_lattice3(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v2_lattice3(A_155)
      | ~ v5_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1838,plain,(
    ! [B_156] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_156,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),B_156,'#skF_3')
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1834])).

tff(c_1848,plain,(
    ! [B_158] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_158,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),B_158,'#skF_3')
      | ~ m1_subset_1(B_158,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_1838])).

tff(c_1862,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1848])).

tff(c_1730,plain,(
    ! [A_143,B_144,C_145] :
      ( r3_orders_2(A_143,B_144,B_144)
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1734,plain,(
    ! [B_144] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_144,B_144)
      | ~ m1_subset_1(B_144,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1'))
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_1730])).

tff(c_1740,plain,(
    ! [B_144] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_144,B_144)
      | ~ m1_subset_1(B_144,u1_struct_0(k2_yellow_1('#skF_1')))
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_1734])).

tff(c_1744,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1740])).

tff(c_1747,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1744,c_6])).

tff(c_1751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_44,c_1747])).

tff(c_1754,plain,(
    ! [B_146] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_1740])).

tff(c_1765,plain,(
    r3_orders_2(k2_yellow_1('#skF_1'),'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1754])).

tff(c_2103,plain,(
    ! [A_171,B_172,C_173] :
      ( k12_lattice3(A_171,B_172,C_173) = B_172
      | ~ r3_orders_2(A_171,B_172,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_171))
      | ~ m1_subset_1(B_172,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | ~ v2_lattice3(A_171)
      | ~ v5_orders_2(A_171)
      | ~ v3_orders_2(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2113,plain,
    ( k12_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ l1_orders_2(k2_yellow_1('#skF_1'))
    | ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ v5_orders_2(k2_yellow_1('#skF_1'))
    | ~ v3_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1765,c_2103])).

tff(c_2128,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_44,c_24,c_40,c_1862,c_2113])).

tff(c_2236,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( k11_lattice3(A_174,k11_lattice3(A_174,B_175,C_176),D_177) = k11_lattice3(A_174,B_175,k11_lattice3(A_174,C_176,D_177))
      | ~ v4_orders_2(A_174)
      | ~ m1_subset_1(D_177,u1_struct_0(A_174))
      | ~ m1_subset_1(C_176,u1_struct_0(A_174))
      | ~ m1_subset_1(B_175,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174)
      | ~ v2_lattice3(A_174)
      | ~ v5_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2246,plain,(
    ! [B_175,C_176] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),B_175,C_176),'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),B_175,k11_lattice3(k2_yellow_1('#skF_1'),C_176,'#skF_2'))
      | ~ v4_orders_2(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_176,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_175,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_42,c_2236])).

tff(c_2427,plain,(
    ! [B_186,C_187] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),B_186,C_187),'#skF_2') = k11_lattice3(k2_yellow_1('#skF_1'),B_186,k11_lattice3(k2_yellow_1('#skF_1'),C_187,'#skF_2'))
      | ~ m1_subset_1(C_187,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ m1_subset_1(B_186,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_30,c_2246])).

tff(c_2466,plain,
    ( k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2128,c_2427])).

tff(c_2496,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_2466])).

tff(c_1906,plain,(
    ! [B_162] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_162,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',B_162)
      | ~ m1_subset_1(B_162,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_1900])).

tff(c_1971,plain,(
    k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1938,c_1906])).

tff(c_1844,plain,(
    ! [B_156] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_156,'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),B_156,'#skF_3')
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44,c_24,c_1838])).

tff(c_1976,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1938,c_1844])).

tff(c_2231,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3',k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1976])).

tff(c_2504,plain,(
    k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') = k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2496,c_2231])).

tff(c_2002,plain,(
    ! [A_164,B_165,C_166] :
      ( r3_orders_2(A_164,B_165,C_166)
      | k12_lattice3(A_164,B_165,C_166) != B_165
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v2_lattice3(A_164)
      | ~ v5_orders_2(A_164)
      | ~ v3_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2008,plain,(
    ! [B_165] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_165,'#skF_3')
      | k12_lattice3(k2_yellow_1('#skF_1'),B_165,'#skF_3') != B_165
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_40,c_2002])).

tff(c_2056,plain,(
    ! [B_169] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_169,'#skF_3')
      | k12_lattice3(k2_yellow_1('#skF_1'),B_169,'#skF_3') != B_169
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_44,c_24,c_2008])).

tff(c_2070,plain,
    ( r3_orders_2(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | k12_lattice3(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') != k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1938,c_2056])).

tff(c_2678,plain,(
    r3_orders_2(k2_yellow_1('#skF_1'),k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2504,c_2070])).

tff(c_2682,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),u1_struct_0(k2_yellow_1('#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2678,c_36])).

tff(c_2688,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_40,c_2682])).

tff(c_2690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1929,c_2688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:36:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.83  
% 4.64/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.83  %$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > g1_orders_2 > #nlpp > u1_struct_0 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_1
% 4.64/1.83  
% 4.64/1.83  %Foreground sorts:
% 4.64/1.83  
% 4.64/1.83  
% 4.64/1.83  %Background operators:
% 4.64/1.83  
% 4.64/1.83  
% 4.64/1.83  %Foreground operators:
% 4.64/1.83  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.64/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.64/1.83  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.64/1.83  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.64/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.83  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.64/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.83  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.64/1.83  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 4.64/1.83  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.64/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.64/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.64/1.83  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.64/1.83  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.64/1.83  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.64/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.83  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.64/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.83  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.64/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.64/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.64/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.83  
% 4.64/1.85  tff(f_163, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.64/1.85  tff(f_136, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.64/1.85  tff(f_128, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.64/1.85  tff(f_85, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 4.64/1.85  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.64/1.85  tff(f_59, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.64/1.85  tff(f_71, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.64/1.85  tff(f_122, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_0)).
% 4.64/1.85  tff(f_44, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 4.64/1.85  tff(f_51, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 4.64/1.85  tff(f_104, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (v4_orders_2(A) => (k11_lattice3(A, k11_lattice3(A, B, C), D) = k11_lattice3(A, B, k11_lattice3(A, C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_lattice3)).
% 4.64/1.85  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.64/1.85  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.64/1.85  tff(c_42, plain, (m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.64/1.85  tff(c_32, plain, (![A_45]: (v5_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.64/1.85  tff(c_44, plain, (v2_lattice3(k2_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.64/1.85  tff(c_24, plain, (![A_44]: (l1_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.64/1.85  tff(c_40, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.64/1.85  tff(c_1896, plain, (![A_160, C_161, B_162]: (k11_lattice3(A_160, C_161, B_162)=k11_lattice3(A_160, B_162, C_161) | ~m1_subset_1(C_161, u1_struct_0(A_160)) | ~m1_subset_1(B_162, u1_struct_0(A_160)) | ~l1_orders_2(A_160) | ~v2_lattice3(A_160) | ~v5_orders_2(A_160))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.64/1.85  tff(c_1900, plain, (![B_162]: (k11_lattice3(k2_yellow_1('#skF_1'), B_162, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', B_162) | ~m1_subset_1(B_162, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1896])).
% 4.64/1.85  tff(c_1910, plain, (![B_163]: (k11_lattice3(k2_yellow_1('#skF_1'), B_163, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', B_163) | ~m1_subset_1(B_163, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_1900])).
% 4.64/1.85  tff(c_1926, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1910])).
% 4.64/1.85  tff(c_160, plain, (![A_81, C_82, B_83]: (k11_lattice3(A_81, C_82, B_83)=k11_lattice3(A_81, B_83, C_82) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~m1_subset_1(B_83, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | ~v2_lattice3(A_81) | ~v5_orders_2(A_81))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.64/1.85  tff(c_164, plain, (![B_83]: (k11_lattice3(k2_yellow_1('#skF_1'), B_83, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', B_83) | ~m1_subset_1(B_83, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_160])).
% 4.64/1.85  tff(c_193, plain, (![B_85]: (k11_lattice3(k2_yellow_1('#skF_1'), B_85, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', B_85) | ~m1_subset_1(B_85, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_164])).
% 4.64/1.85  tff(c_209, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_193])).
% 4.64/1.85  tff(c_63, plain, (![A_64, B_65, C_66]: (r1_tarski(A_64, k3_xboole_0(B_65, C_66)) | ~r1_tarski(A_64, C_66) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.85  tff(c_38, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.64/1.85  tff(c_67, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_63, c_38])).
% 4.64/1.85  tff(c_68, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 4.64/1.85  tff(c_210, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_68])).
% 4.64/1.85  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k11_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.64/1.85  tff(c_215, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_8])).
% 4.64/1.85  tff(c_219, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_40, c_215])).
% 4.64/1.85  tff(c_166, plain, (![B_83]: (k11_lattice3(k2_yellow_1('#skF_1'), B_83, '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', B_83) | ~m1_subset_1(B_83, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_160])).
% 4.64/1.85  tff(c_281, plain, (![B_89]: (k11_lattice3(k2_yellow_1('#skF_1'), B_89, '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', B_89) | ~m1_subset_1(B_89, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_166])).
% 4.64/1.85  tff(c_295, plain, (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_219, c_281])).
% 4.64/1.85  tff(c_262, plain, (![A_86, B_87, C_88]: (k12_lattice3(A_86, B_87, C_88)=k11_lattice3(A_86, B_87, C_88) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v2_lattice3(A_86) | ~v5_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.85  tff(c_270, plain, (![B_87]: (k12_lattice3(k2_yellow_1('#skF_1'), B_87, '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), B_87, '#skF_2') | ~m1_subset_1(B_87, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_262])).
% 4.64/1.85  tff(c_332, plain, (![B_91]: (k12_lattice3(k2_yellow_1('#skF_1'), B_91, '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), B_91, '#skF_2') | ~m1_subset_1(B_91, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_270])).
% 4.64/1.85  tff(c_346, plain, (k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_219, c_332])).
% 4.64/1.85  tff(c_1474, plain, (k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_346])).
% 4.64/1.85  tff(c_28, plain, (![A_45]: (v3_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.64/1.85  tff(c_1220, plain, (![A_117, B_118, C_119]: (r3_orders_2(A_117, B_118, C_119) | k12_lattice3(A_117, B_118, C_119)!=B_118 | ~m1_subset_1(C_119, u1_struct_0(A_117)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_orders_2(A_117) | ~v2_lattice3(A_117) | ~v5_orders_2(A_117) | ~v3_orders_2(A_117))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.64/1.85  tff(c_1230, plain, (![B_118]: (r3_orders_2(k2_yellow_1('#skF_1'), B_118, '#skF_2') | k12_lattice3(k2_yellow_1('#skF_1'), B_118, '#skF_2')!=B_118 | ~m1_subset_1(B_118, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_1220])).
% 4.64/1.85  tff(c_1279, plain, (![B_122]: (r3_orders_2(k2_yellow_1('#skF_1'), B_122, '#skF_2') | k12_lattice3(k2_yellow_1('#skF_1'), B_122, '#skF_2')!=B_122 | ~m1_subset_1(B_122, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_44, c_24, c_1230])).
% 4.64/1.85  tff(c_1297, plain, (r3_orders_2(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2') | k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')!=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_219, c_1279])).
% 4.64/1.85  tff(c_1639, plain, (r3_orders_2(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2') | k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))!=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_1297])).
% 4.64/1.85  tff(c_1640, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))!=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1639])).
% 4.64/1.85  tff(c_351, plain, (k12_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_332])).
% 4.64/1.85  tff(c_70, plain, (![A_70, B_71, C_72]: (r3_orders_2(A_70, B_71, B_71) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.64/1.85  tff(c_74, plain, (![B_71]: (r3_orders_2(k2_yellow_1('#skF_1'), B_71, B_71) | ~m1_subset_1(B_71, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')) | v2_struct_0(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_70])).
% 4.64/1.85  tff(c_80, plain, (![B_71]: (r3_orders_2(k2_yellow_1('#skF_1'), B_71, B_71) | ~m1_subset_1(B_71, u1_struct_0(k2_yellow_1('#skF_1'))) | v2_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_74])).
% 4.64/1.85  tff(c_84, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_80])).
% 4.64/1.85  tff(c_6, plain, (![A_7]: (~v2_struct_0(A_7) | ~v2_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.64/1.85  tff(c_87, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_6])).
% 4.64/1.85  tff(c_91, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_44, c_87])).
% 4.64/1.85  tff(c_98, plain, (![B_73]: (r3_orders_2(k2_yellow_1('#skF_1'), B_73, B_73) | ~m1_subset_1(B_73, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_80])).
% 4.64/1.85  tff(c_110, plain, (r3_orders_2(k2_yellow_1('#skF_1'), '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_98])).
% 4.64/1.85  tff(c_1376, plain, (![A_123, B_124, C_125]: (k12_lattice3(A_123, B_124, C_125)=B_124 | ~r3_orders_2(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v2_lattice3(A_123) | ~v5_orders_2(A_123) | ~v3_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.64/1.85  tff(c_1386, plain, (k12_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_110, c_1376])).
% 4.64/1.85  tff(c_1403, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_44, c_24, c_42, c_351, c_1386])).
% 4.64/1.85  tff(c_30, plain, (![A_45]: (v4_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.64/1.85  tff(c_1479, plain, (![A_127, B_128, C_129, D_130]: (k11_lattice3(A_127, k11_lattice3(A_127, B_128, C_129), D_130)=k11_lattice3(A_127, B_128, k11_lattice3(A_127, C_129, D_130)) | ~v4_orders_2(A_127) | ~m1_subset_1(D_130, u1_struct_0(A_127)) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127) | ~v2_lattice3(A_127) | ~v5_orders_2(A_127))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.64/1.85  tff(c_1487, plain, (![B_128, C_129]: (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), B_128, C_129), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), B_128, k11_lattice3(k2_yellow_1('#skF_1'), C_129, '#skF_3')) | ~v4_orders_2(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_129, u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(B_128, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1479])).
% 4.64/1.85  tff(c_1641, plain, (![B_138, C_139]: (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), B_138, C_139), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), B_138, k11_lattice3(k2_yellow_1('#skF_1'), C_139, '#skF_3')) | ~m1_subset_1(C_139, u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(B_138, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_30, c_1487])).
% 4.64/1.85  tff(c_1680, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'))=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3') | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1403, c_1641])).
% 4.64/1.85  tff(c_1710, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_209, c_209, c_1680])).
% 4.64/1.85  tff(c_1712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1640, c_1710])).
% 4.64/1.85  tff(c_1713, plain, (r3_orders_2(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_1639])).
% 4.64/1.85  tff(c_36, plain, (![B_50, C_52, A_46]: (r1_tarski(B_50, C_52) | ~r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.64/1.85  tff(c_1718, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1'))) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1713, c_36])).
% 4.64/1.85  tff(c_1724, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_42, c_1718])).
% 4.64/1.85  tff(c_1726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_210, c_1724])).
% 4.64/1.85  tff(c_1727, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 4.64/1.85  tff(c_1929, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1727])).
% 4.64/1.85  tff(c_1934, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1926, c_8])).
% 4.64/1.85  tff(c_1938, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_42, c_40, c_1934])).
% 4.64/1.85  tff(c_1834, plain, (![A_155, B_156, C_157]: (k12_lattice3(A_155, B_156, C_157)=k11_lattice3(A_155, B_156, C_157) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v2_lattice3(A_155) | ~v5_orders_2(A_155))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.64/1.85  tff(c_1838, plain, (![B_156]: (k12_lattice3(k2_yellow_1('#skF_1'), B_156, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), B_156, '#skF_3') | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1834])).
% 4.64/1.85  tff(c_1848, plain, (![B_158]: (k12_lattice3(k2_yellow_1('#skF_1'), B_158, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), B_158, '#skF_3') | ~m1_subset_1(B_158, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_1838])).
% 4.64/1.85  tff(c_1862, plain, (k12_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_1848])).
% 4.64/1.85  tff(c_1730, plain, (![A_143, B_144, C_145]: (r3_orders_2(A_143, B_144, B_144) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.64/1.85  tff(c_1734, plain, (![B_144]: (r3_orders_2(k2_yellow_1('#skF_1'), B_144, B_144) | ~m1_subset_1(B_144, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')) | v2_struct_0(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_1730])).
% 4.64/1.85  tff(c_1740, plain, (![B_144]: (r3_orders_2(k2_yellow_1('#skF_1'), B_144, B_144) | ~m1_subset_1(B_144, u1_struct_0(k2_yellow_1('#skF_1'))) | v2_struct_0(k2_yellow_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_1734])).
% 4.64/1.85  tff(c_1744, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1740])).
% 4.64/1.85  tff(c_1747, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_1744, c_6])).
% 4.64/1.85  tff(c_1751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_44, c_1747])).
% 4.64/1.85  tff(c_1754, plain, (![B_146]: (r3_orders_2(k2_yellow_1('#skF_1'), B_146, B_146) | ~m1_subset_1(B_146, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_1740])).
% 4.64/1.85  tff(c_1765, plain, (r3_orders_2(k2_yellow_1('#skF_1'), '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_1754])).
% 4.64/1.85  tff(c_2103, plain, (![A_171, B_172, C_173]: (k12_lattice3(A_171, B_172, C_173)=B_172 | ~r3_orders_2(A_171, B_172, C_173) | ~m1_subset_1(C_173, u1_struct_0(A_171)) | ~m1_subset_1(B_172, u1_struct_0(A_171)) | ~l1_orders_2(A_171) | ~v2_lattice3(A_171) | ~v5_orders_2(A_171) | ~v3_orders_2(A_171))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.64/1.85  tff(c_2113, plain, (k12_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_1765, c_2103])).
% 4.64/1.85  tff(c_2128, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_44, c_24, c_40, c_1862, c_2113])).
% 4.64/1.85  tff(c_2236, plain, (![A_174, B_175, C_176, D_177]: (k11_lattice3(A_174, k11_lattice3(A_174, B_175, C_176), D_177)=k11_lattice3(A_174, B_175, k11_lattice3(A_174, C_176, D_177)) | ~v4_orders_2(A_174) | ~m1_subset_1(D_177, u1_struct_0(A_174)) | ~m1_subset_1(C_176, u1_struct_0(A_174)) | ~m1_subset_1(B_175, u1_struct_0(A_174)) | ~l1_orders_2(A_174) | ~v2_lattice3(A_174) | ~v5_orders_2(A_174))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.64/1.85  tff(c_2246, plain, (![B_175, C_176]: (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), B_175, C_176), '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), B_175, k11_lattice3(k2_yellow_1('#skF_1'), C_176, '#skF_2')) | ~v4_orders_2(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_176, u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(B_175, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_42, c_2236])).
% 4.64/1.85  tff(c_2427, plain, (![B_186, C_187]: (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), B_186, C_187), '#skF_2')=k11_lattice3(k2_yellow_1('#skF_1'), B_186, k11_lattice3(k2_yellow_1('#skF_1'), C_187, '#skF_2')) | ~m1_subset_1(C_187, u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(B_186, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_30, c_2246])).
% 4.64/1.85  tff(c_2466, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2128, c_2427])).
% 4.64/1.85  tff(c_2496, plain, (k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_2466])).
% 4.64/1.85  tff(c_1906, plain, (![B_162]: (k11_lattice3(k2_yellow_1('#skF_1'), B_162, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', B_162) | ~m1_subset_1(B_162, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_1900])).
% 4.64/1.85  tff(c_1971, plain, (k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_1938, c_1906])).
% 4.64/1.85  tff(c_1844, plain, (![B_156]: (k12_lattice3(k2_yellow_1('#skF_1'), B_156, '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), B_156, '#skF_3') | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_44, c_24, c_1838])).
% 4.64/1.85  tff(c_1976, plain, (k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1938, c_1844])).
% 4.64/1.85  tff(c_2231, plain, (k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1976])).
% 4.64/1.85  tff(c_2504, plain, (k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2496, c_2231])).
% 4.64/1.85  tff(c_2002, plain, (![A_164, B_165, C_166]: (r3_orders_2(A_164, B_165, C_166) | k12_lattice3(A_164, B_165, C_166)!=B_165 | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v2_lattice3(A_164) | ~v5_orders_2(A_164) | ~v3_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.64/1.85  tff(c_2008, plain, (![B_165]: (r3_orders_2(k2_yellow_1('#skF_1'), B_165, '#skF_3') | k12_lattice3(k2_yellow_1('#skF_1'), B_165, '#skF_3')!=B_165 | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_40, c_2002])).
% 4.64/1.85  tff(c_2056, plain, (![B_169]: (r3_orders_2(k2_yellow_1('#skF_1'), B_169, '#skF_3') | k12_lattice3(k2_yellow_1('#skF_1'), B_169, '#skF_3')!=B_169 | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_44, c_24, c_2008])).
% 4.64/1.85  tff(c_2070, plain, (r3_orders_2(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | k12_lattice3(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')!=k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1938, c_2056])).
% 4.64/1.85  tff(c_2678, plain, (r3_orders_2(k2_yellow_1('#skF_1'), k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2504, c_2070])).
% 4.64/1.85  tff(c_2682, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), u1_struct_0(k2_yellow_1('#skF_1'))) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2678, c_36])).
% 4.64/1.85  tff(c_2688, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1938, c_40, c_2682])).
% 4.64/1.85  tff(c_2690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1929, c_2688])).
% 4.64/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.85  
% 4.64/1.85  Inference rules
% 4.64/1.85  ----------------------
% 4.64/1.85  #Ref     : 0
% 4.64/1.85  #Sup     : 570
% 4.64/1.85  #Fact    : 0
% 4.64/1.85  #Define  : 0
% 4.64/1.85  #Split   : 16
% 4.64/1.85  #Chain   : 0
% 4.64/1.85  #Close   : 0
% 4.64/1.85  
% 4.64/1.85  Ordering : KBO
% 4.64/1.85  
% 4.64/1.85  Simplification rules
% 4.64/1.85  ----------------------
% 4.64/1.85  #Subsume      : 17
% 4.64/1.85  #Demod        : 1131
% 4.64/1.85  #Tautology    : 300
% 4.64/1.85  #SimpNegUnit  : 58
% 4.64/1.85  #BackRed      : 33
% 4.64/1.85  
% 4.64/1.85  #Partial instantiations: 0
% 4.64/1.85  #Strategies tried      : 1
% 4.64/1.85  
% 4.64/1.85  Timing (in seconds)
% 4.64/1.85  ----------------------
% 4.64/1.85  Preprocessing        : 0.35
% 4.64/1.85  Parsing              : 0.19
% 4.64/1.85  CNF conversion       : 0.03
% 4.64/1.85  Main loop            : 0.71
% 4.64/1.85  Inferencing          : 0.22
% 4.64/1.86  Reduction            : 0.28
% 4.64/1.86  Demodulation         : 0.21
% 4.64/1.86  BG Simplification    : 0.03
% 4.64/1.86  Subsumption          : 0.12
% 4.64/1.86  Abstraction          : 0.04
% 4.64/1.86  MUC search           : 0.00
% 4.64/1.86  Cooper               : 0.00
% 4.64/1.86  Total                : 1.11
% 4.64/1.86  Index Insertion      : 0.00
% 4.64/1.86  Index Deletion       : 0.00
% 4.64/1.86  Index Matching       : 0.00
% 4.64/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
