%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:38 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   66 (  97 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  101 ( 184 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > r1_tarski > m1_subset_1 > v3_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
           => ( r1_lattices(k1_lattice3(A),B,C)
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( k1_lattices(k1_lattice3(A),B,C) = k2_xboole_0(B,C)
            & k2_lattices(k1_lattice3(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_lattice3)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_64,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_60,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_42,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_75,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_96,plain,(
    ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_36])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_75,c_10])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_193,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_lattices(k1_lattice3(A_47),B_48,C_49) = k2_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(k1_lattice3(A_47)))
      | ~ m1_subset_1(B_48,u1_struct_0(k1_lattice3(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1076,plain,(
    ! [B_106] :
      ( k1_lattices(k1_lattice3('#skF_1'),B_106,'#skF_3') = k2_xboole_0(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_1079,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1076])).

tff(c_1084,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1079])).

tff(c_24,plain,(
    ! [A_17] : ~ v2_struct_0(k1_lattice3(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_16] : l3_lattices(k1_lattice3(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    ! [A_28] :
      ( l2_lattices(A_28)
      | ~ l3_lattices(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,(
    ! [A_16] : l2_lattices(k1_lattice3(A_16)) ),
    inference(resolution,[status(thm)],[c_22,c_54])).

tff(c_511,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_lattices(A_73,B_74,C_75)
      | k1_lattices(A_73,B_74,C_75) != C_75
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l2_lattices(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_515,plain,(
    ! [B_74] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_74,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l2_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_32,c_511])).

tff(c_522,plain,(
    ! [B_74] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_74,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_74,u1_struct_0(k1_lattice3('#skF_1')))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_515])).

tff(c_1160,plain,(
    ! [B_111] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_111,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_111,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_111,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_522])).

tff(c_1163,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_1160])).

tff(c_1169,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1163])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1169])).

tff(c_1173,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1603,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_lattices(k1_lattice3(A_151),B_152,C_153) = k2_xboole_0(B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(k1_lattice3(A_151)))
      | ~ m1_subset_1(B_152,u1_struct_0(k1_lattice3(A_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1645,plain,(
    ! [B_156] :
      ( k1_lattices(k1_lattice3('#skF_1'),B_156,'#skF_3') = k2_xboole_0(B_156,'#skF_3')
      | ~ m1_subset_1(B_156,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_1603])).

tff(c_1652,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1645])).

tff(c_1172,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1809,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_lattices(A_170,B_171,C_172) = C_172
      | ~ r1_lattices(A_170,B_171,C_172)
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | ~ l2_lattices(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1813,plain,
    ( k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ l2_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1172,c_1809])).

tff(c_1820,plain,
    ( k2_xboole_0('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34,c_32,c_1652,c_1813])).

tff(c_1821,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1820])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1183,plain,(
    ! [A_114,C_115,B_116] :
      ( r1_tarski(A_114,C_115)
      | ~ r1_tarski(k2_xboole_0(A_114,B_116),C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1191,plain,(
    ! [A_114,B_116] : r1_tarski(A_114,k2_xboole_0(A_114,B_116)) ),
    inference(resolution,[status(thm)],[c_6,c_1183])).

tff(c_1856,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_1191])).

tff(c_1867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1173,c_1856])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.58  
% 3.49/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.58  %$ r1_lattices > r1_tarski > m1_subset_1 > v3_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 3.49/1.58  
% 3.49/1.58  %Foreground sorts:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Background operators:
% 3.49/1.58  
% 3.49/1.58  
% 3.49/1.58  %Foreground operators:
% 3.49/1.58  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.49/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.49/1.58  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 3.49/1.58  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.58  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.49/1.58  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.49/1.58  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.49/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.58  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.58  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.49/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.49/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.49/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.49/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.58  
% 3.49/1.59  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => (r1_lattices(k1_lattice3(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_lattice3)).
% 3.49/1.59  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.49/1.59  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => ((k1_lattices(k1_lattice3(A), B, C) = k2_xboole_0(B, C)) & (k2_lattices(k1_lattice3(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_lattice3)).
% 3.49/1.59  tff(f_69, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 3.49/1.59  tff(f_64, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 3.49/1.59  tff(f_60, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.49/1.59  tff(f_54, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 3.49/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.59  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.49/1.59  tff(c_42, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.49/1.59  tff(c_75, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.49/1.59  tff(c_36, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.49/1.59  tff(c_96, plain, (~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_36])).
% 3.49/1.59  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.59  tff(c_79, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_75, c_10])).
% 3.49/1.59  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.49/1.59  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.49/1.59  tff(c_193, plain, (![A_47, B_48, C_49]: (k1_lattices(k1_lattice3(A_47), B_48, C_49)=k2_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(k1_lattice3(A_47))) | ~m1_subset_1(B_48, u1_struct_0(k1_lattice3(A_47))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.49/1.59  tff(c_1076, plain, (![B_106]: (k1_lattices(k1_lattice3('#skF_1'), B_106, '#skF_3')=k2_xboole_0(B_106, '#skF_3') | ~m1_subset_1(B_106, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_193])).
% 3.49/1.59  tff(c_1079, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_1076])).
% 3.49/1.59  tff(c_1084, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1079])).
% 3.49/1.59  tff(c_24, plain, (![A_17]: (~v2_struct_0(k1_lattice3(A_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.49/1.59  tff(c_22, plain, (![A_16]: (l3_lattices(k1_lattice3(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.59  tff(c_54, plain, (![A_28]: (l2_lattices(A_28) | ~l3_lattices(A_28))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.59  tff(c_58, plain, (![A_16]: (l2_lattices(k1_lattice3(A_16)))), inference(resolution, [status(thm)], [c_22, c_54])).
% 3.49/1.59  tff(c_511, plain, (![A_73, B_74, C_75]: (r1_lattices(A_73, B_74, C_75) | k1_lattices(A_73, B_74, C_75)!=C_75 | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l2_lattices(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.59  tff(c_515, plain, (![B_74]: (r1_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3')!='#skF_3' | ~m1_subset_1(B_74, u1_struct_0(k1_lattice3('#skF_1'))) | ~l2_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_32, c_511])).
% 3.49/1.59  tff(c_522, plain, (![B_74]: (r1_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_74, '#skF_3')!='#skF_3' | ~m1_subset_1(B_74, u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_515])).
% 3.49/1.59  tff(c_1160, plain, (![B_111]: (r1_lattices(k1_lattice3('#skF_1'), B_111, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_111, '#skF_3')!='#skF_3' | ~m1_subset_1(B_111, u1_struct_0(k1_lattice3('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_24, c_522])).
% 3.49/1.59  tff(c_1163, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_34, c_1160])).
% 3.49/1.59  tff(c_1169, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1163])).
% 3.49/1.59  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_1169])).
% 3.49/1.59  tff(c_1173, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.49/1.59  tff(c_1603, plain, (![A_151, B_152, C_153]: (k1_lattices(k1_lattice3(A_151), B_152, C_153)=k2_xboole_0(B_152, C_153) | ~m1_subset_1(C_153, u1_struct_0(k1_lattice3(A_151))) | ~m1_subset_1(B_152, u1_struct_0(k1_lattice3(A_151))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.49/1.59  tff(c_1645, plain, (![B_156]: (k1_lattices(k1_lattice3('#skF_1'), B_156, '#skF_3')=k2_xboole_0(B_156, '#skF_3') | ~m1_subset_1(B_156, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_32, c_1603])).
% 3.49/1.59  tff(c_1652, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_1645])).
% 3.49/1.59  tff(c_1172, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.49/1.59  tff(c_1809, plain, (![A_170, B_171, C_172]: (k1_lattices(A_170, B_171, C_172)=C_172 | ~r1_lattices(A_170, B_171, C_172) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | ~l2_lattices(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.49/1.59  tff(c_1813, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l2_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_1172, c_1809])).
% 3.49/1.59  tff(c_1820, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34, c_32, c_1652, c_1813])).
% 3.49/1.59  tff(c_1821, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24, c_1820])).
% 3.49/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.59  tff(c_1183, plain, (![A_114, C_115, B_116]: (r1_tarski(A_114, C_115) | ~r1_tarski(k2_xboole_0(A_114, B_116), C_115))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.59  tff(c_1191, plain, (![A_114, B_116]: (r1_tarski(A_114, k2_xboole_0(A_114, B_116)))), inference(resolution, [status(thm)], [c_6, c_1183])).
% 3.49/1.59  tff(c_1856, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1821, c_1191])).
% 3.49/1.59  tff(c_1867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1173, c_1856])).
% 3.49/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.59  
% 3.49/1.59  Inference rules
% 3.49/1.59  ----------------------
% 3.49/1.59  #Ref     : 0
% 3.49/1.59  #Sup     : 423
% 3.49/1.59  #Fact    : 0
% 3.49/1.59  #Define  : 0
% 3.49/1.59  #Split   : 3
% 3.49/1.59  #Chain   : 0
% 3.49/1.59  #Close   : 0
% 3.49/1.59  
% 3.49/1.59  Ordering : KBO
% 3.49/1.59  
% 3.49/1.59  Simplification rules
% 3.49/1.59  ----------------------
% 3.49/1.59  #Subsume      : 54
% 3.49/1.59  #Demod        : 235
% 3.49/1.59  #Tautology    : 206
% 3.49/1.59  #SimpNegUnit  : 8
% 3.49/1.59  #BackRed      : 1
% 3.49/1.59  
% 3.49/1.59  #Partial instantiations: 0
% 3.49/1.59  #Strategies tried      : 1
% 3.49/1.59  
% 3.49/1.59  Timing (in seconds)
% 3.49/1.59  ----------------------
% 3.49/1.60  Preprocessing        : 0.28
% 3.49/1.60  Parsing              : 0.15
% 3.49/1.60  CNF conversion       : 0.02
% 3.49/1.60  Main loop            : 0.50
% 3.49/1.60  Inferencing          : 0.19
% 3.49/1.60  Reduction            : 0.17
% 3.49/1.60  Demodulation         : 0.13
% 3.49/1.60  BG Simplification    : 0.02
% 3.49/1.60  Subsumption          : 0.08
% 3.49/1.60  Abstraction          : 0.03
% 3.49/1.60  MUC search           : 0.00
% 3.49/1.60  Cooper               : 0.00
% 3.49/1.60  Total                : 0.81
% 3.49/1.60  Index Insertion      : 0.00
% 3.49/1.60  Index Deletion       : 0.00
% 3.49/1.60  Index Matching       : 0.00
% 3.49/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
