%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:43 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 211 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 669 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattice3 > r1_lattice3 > m1_subset_1 > v2_struct_0 > v10_lattices > l3_lattices > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(k5_lattice3,type,(
    k5_lattice3: ( $i * $i ) > $i )).

tff(k4_lattice3,type,(
    k4_lattice3: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( ( ~ v2_struct_0(B)
          & v10_lattices(B)
          & l3_lattices(B) )
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k3_lattice3(B)))
           => ( r1_lattice3(k3_lattice3(B),A,C)
            <=> r3_lattice3(B,k5_lattice3(B,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_lattice3)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k3_lattice3(A)))
         => k5_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattice3)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(k3_lattice3(A))) )
     => m1_subset_1(k5_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattice3)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k4_lattice3(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & l3_lattices(B) )
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(B))
         => ( r3_lattice3(B,C,A)
          <=> r1_lattice3(k3_lattice3(B),A,k4_lattice3(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_lattice3)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_16,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_126,plain,(
    ! [A_32,B_33] :
      ( k5_lattice3(A_32,B_33) = B_33
      | ~ m1_subset_1(B_33,u1_struct_0(k3_lattice3(A_32)))
      | ~ l3_lattices(A_32)
      | ~ v10_lattices(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_129,plain,
    ( k5_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_126])).

tff(c_132,plain,
    ( k5_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_129])).

tff(c_133,plain,(
    k5_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_132])).

tff(c_35,plain,(
    ! [A_16,B_17] :
      ( k5_lattice3(A_16,B_17) = B_17
      | ~ m1_subset_1(B_17,u1_struct_0(k3_lattice3(A_16)))
      | ~ l3_lattices(A_16)
      | ~ v10_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,
    ( k5_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_35])).

tff(c_41,plain,
    ( k5_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_38])).

tff(c_42,plain,(
    k5_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_41])).

tff(c_20,plain,
    ( ~ r3_lattice3('#skF_2',k5_lattice3('#skF_2','#skF_3'),'#skF_1')
    | ~ r1_lattice3(k3_lattice3('#skF_2'),'#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_27,plain,(
    ~ r1_lattice3(k3_lattice3('#skF_2'),'#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,
    ( r1_lattice3(k3_lattice3('#skF_2'),'#skF_1','#skF_3')
    | r3_lattice3('#skF_2',k5_lattice3('#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    r3_lattice3('#skF_2',k5_lattice3('#skF_2','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_26])).

tff(c_43,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_48,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k5_lattice3(A_18,B_19),u1_struct_0(A_18))
      | ~ m1_subset_1(B_19,u1_struct_0(k3_lattice3(A_18)))
      | ~ l3_lattices(A_18)
      | ~ v10_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,
    ( m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_62,plain,
    ( m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_58])).

tff(c_63,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_62])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k4_lattice3(A_1,B_3) = B_3
      | ~ m1_subset_1(B_3,u1_struct_0(A_1))
      | ~ l3_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_69,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_66])).

tff(c_70,plain,(
    k4_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_69])).

tff(c_94,plain,(
    ! [B_26,A_27,C_28] :
      ( r1_lattice3(k3_lattice3(B_26),A_27,k4_lattice3(B_26,C_28))
      | ~ r3_lattice3(B_26,C_28,A_27)
      | ~ m1_subset_1(C_28,u1_struct_0(B_26))
      | ~ l3_lattices(B_26)
      | ~ v10_lattices(B_26)
      | v2_struct_0(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_100,plain,(
    ! [A_27] :
      ( r1_lattice3(k3_lattice3('#skF_2'),A_27,'#skF_3')
      | ~ r3_lattice3('#skF_2','#skF_3',A_27)
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_103,plain,(
    ! [A_27] :
      ( r1_lattice3(k3_lattice3('#skF_2'),A_27,'#skF_3')
      | ~ r3_lattice3('#skF_2','#skF_3',A_27)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_63,c_100])).

tff(c_105,plain,(
    ! [A_29] :
      ( r1_lattice3(k3_lattice3('#skF_2'),A_29,'#skF_3')
      | ~ r3_lattice3('#skF_2','#skF_3',A_29) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_103])).

tff(c_111,plain,(
    ~ r3_lattice3('#skF_2','#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_105,c_27])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_111])).

tff(c_117,plain,(
    ~ r3_lattice3('#skF_2',k5_lattice3('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_134,plain,(
    ~ r3_lattice3('#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_117])).

tff(c_118,plain,(
    r1_lattice3(k3_lattice3('#skF_2'),'#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_140,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k5_lattice3(A_34,B_35),u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(k3_lattice3(A_34)))
      | ~ l3_lattices(A_34)
      | ~ v10_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,
    ( m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k3_lattice3('#skF_2')))
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_140])).

tff(c_154,plain,
    ( m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_150])).

tff(c_155,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_154])).

tff(c_158,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_161,plain,
    ( k4_lattice3('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_158])).

tff(c_162,plain,(
    k4_lattice3('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_161])).

tff(c_178,plain,(
    ! [B_38,C_39,A_40] :
      ( r3_lattice3(B_38,C_39,A_40)
      | ~ r1_lattice3(k3_lattice3(B_38),A_40,k4_lattice3(B_38,C_39))
      | ~ m1_subset_1(C_39,u1_struct_0(B_38))
      | ~ l3_lattices(B_38)
      | ~ v10_lattices(B_38)
      | v2_struct_0(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_181,plain,(
    ! [A_40] :
      ( r3_lattice3('#skF_2','#skF_3',A_40)
      | ~ r1_lattice3(k3_lattice3('#skF_2'),A_40,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l3_lattices('#skF_2')
      | ~ v10_lattices('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_178])).

tff(c_183,plain,(
    ! [A_40] :
      ( r3_lattice3('#skF_2','#skF_3',A_40)
      | ~ r1_lattice3(k3_lattice3('#skF_2'),A_40,'#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_155,c_181])).

tff(c_196,plain,(
    ! [A_44] :
      ( r3_lattice3('#skF_2','#skF_3',A_44)
      | ~ r1_lattice3(k3_lattice3('#skF_2'),A_44,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_183])).

tff(c_199,plain,(
    r3_lattice3('#skF_2','#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_118,c_196])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.22  %$ r3_lattice3 > r1_lattice3 > m1_subset_1 > v2_struct_0 > v10_lattices > l3_lattices > k5_lattice3 > k4_lattice3 > #nlpp > u1_struct_0 > k3_lattice3 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.22  
% 2.01/1.22  %Foreground sorts:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Background operators:
% 2.01/1.22  
% 2.01/1.22  
% 2.01/1.22  %Foreground operators:
% 2.01/1.22  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.01/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.22  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.01/1.22  tff(k5_lattice3, type, k5_lattice3: ($i * $i) > $i).
% 2.01/1.22  tff(k4_lattice3, type, k4_lattice3: ($i * $i) > $i).
% 2.01/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.22  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.01/1.22  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.22  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.01/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.22  
% 2.13/1.24  tff(f_89, negated_conjecture, ~(![A, B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (![C]: (m1_subset_1(C, u1_struct_0(k3_lattice3(B))) => (r1_lattice3(k3_lattice3(B), A, C) <=> r3_lattice3(B, k5_lattice3(B, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_lattice3)).
% 2.13/1.24  tff(f_49, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k3_lattice3(A))) => (k5_lattice3(A, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_lattice3)).
% 2.13/1.24  tff(f_60, axiom, (![A, B]: ((((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(k3_lattice3(A)))) => m1_subset_1(k5_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 2.13/1.24  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattice3(A, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattice3)).
% 2.13/1.24  tff(f_74, axiom, (![A, B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (r3_lattice3(B, C, A) <=> r1_lattice3(k3_lattice3(B), A, k4_lattice3(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_lattice3)).
% 2.13/1.24  tff(c_18, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_16, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_14, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_12, plain, (m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_126, plain, (![A_32, B_33]: (k5_lattice3(A_32, B_33)=B_33 | ~m1_subset_1(B_33, u1_struct_0(k3_lattice3(A_32))) | ~l3_lattices(A_32) | ~v10_lattices(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.24  tff(c_129, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_126])).
% 2.13/1.24  tff(c_132, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_129])).
% 2.13/1.24  tff(c_133, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_132])).
% 2.13/1.24  tff(c_35, plain, (![A_16, B_17]: (k5_lattice3(A_16, B_17)=B_17 | ~m1_subset_1(B_17, u1_struct_0(k3_lattice3(A_16))) | ~l3_lattices(A_16) | ~v10_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.24  tff(c_38, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_35])).
% 2.13/1.24  tff(c_41, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_38])).
% 2.13/1.24  tff(c_42, plain, (k5_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_41])).
% 2.13/1.24  tff(c_20, plain, (~r3_lattice3('#skF_2', k5_lattice3('#skF_2', '#skF_3'), '#skF_1') | ~r1_lattice3(k3_lattice3('#skF_2'), '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_27, plain, (~r1_lattice3(k3_lattice3('#skF_2'), '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 2.13/1.24  tff(c_26, plain, (r1_lattice3(k3_lattice3('#skF_2'), '#skF_1', '#skF_3') | r3_lattice3('#skF_2', k5_lattice3('#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.13/1.24  tff(c_28, plain, (r3_lattice3('#skF_2', k5_lattice3('#skF_2', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_27, c_26])).
% 2.13/1.24  tff(c_43, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28])).
% 2.13/1.24  tff(c_48, plain, (![A_18, B_19]: (m1_subset_1(k5_lattice3(A_18, B_19), u1_struct_0(A_18)) | ~m1_subset_1(B_19, u1_struct_0(k3_lattice3(A_18))) | ~l3_lattices(A_18) | ~v10_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.24  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_48])).
% 2.13/1.24  tff(c_62, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_58])).
% 2.13/1.24  tff(c_63, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_62])).
% 2.13/1.24  tff(c_2, plain, (![A_1, B_3]: (k4_lattice3(A_1, B_3)=B_3 | ~m1_subset_1(B_3, u1_struct_0(A_1)) | ~l3_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_66, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.13/1.24  tff(c_69, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_66])).
% 2.13/1.24  tff(c_70, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_69])).
% 2.13/1.24  tff(c_94, plain, (![B_26, A_27, C_28]: (r1_lattice3(k3_lattice3(B_26), A_27, k4_lattice3(B_26, C_28)) | ~r3_lattice3(B_26, C_28, A_27) | ~m1_subset_1(C_28, u1_struct_0(B_26)) | ~l3_lattices(B_26) | ~v10_lattices(B_26) | v2_struct_0(B_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.24  tff(c_100, plain, (![A_27]: (r1_lattice3(k3_lattice3('#skF_2'), A_27, '#skF_3') | ~r3_lattice3('#skF_2', '#skF_3', A_27) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_94])).
% 2.13/1.24  tff(c_103, plain, (![A_27]: (r1_lattice3(k3_lattice3('#skF_2'), A_27, '#skF_3') | ~r3_lattice3('#skF_2', '#skF_3', A_27) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_63, c_100])).
% 2.13/1.24  tff(c_105, plain, (![A_29]: (r1_lattice3(k3_lattice3('#skF_2'), A_29, '#skF_3') | ~r3_lattice3('#skF_2', '#skF_3', A_29))), inference(negUnitSimplification, [status(thm)], [c_18, c_103])).
% 2.13/1.24  tff(c_111, plain, (~r3_lattice3('#skF_2', '#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_105, c_27])).
% 2.13/1.24  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43, c_111])).
% 2.13/1.24  tff(c_117, plain, (~r3_lattice3('#skF_2', k5_lattice3('#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 2.13/1.24  tff(c_134, plain, (~r3_lattice3('#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_117])).
% 2.13/1.24  tff(c_118, plain, (r1_lattice3(k3_lattice3('#skF_2'), '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.13/1.24  tff(c_140, plain, (![A_34, B_35]: (m1_subset_1(k5_lattice3(A_34, B_35), u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(k3_lattice3(A_34))) | ~l3_lattices(A_34) | ~v10_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.24  tff(c_150, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0(k3_lattice3('#skF_2'))) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_140])).
% 2.13/1.24  tff(c_154, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_150])).
% 2.13/1.24  tff(c_155, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_154])).
% 2.13/1.24  tff(c_158, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_155, c_2])).
% 2.13/1.24  tff(c_161, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_158])).
% 2.13/1.24  tff(c_162, plain, (k4_lattice3('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_161])).
% 2.13/1.24  tff(c_178, plain, (![B_38, C_39, A_40]: (r3_lattice3(B_38, C_39, A_40) | ~r1_lattice3(k3_lattice3(B_38), A_40, k4_lattice3(B_38, C_39)) | ~m1_subset_1(C_39, u1_struct_0(B_38)) | ~l3_lattices(B_38) | ~v10_lattices(B_38) | v2_struct_0(B_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.13/1.24  tff(c_181, plain, (![A_40]: (r3_lattice3('#skF_2', '#skF_3', A_40) | ~r1_lattice3(k3_lattice3('#skF_2'), A_40, '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_178])).
% 2.13/1.24  tff(c_183, plain, (![A_40]: (r3_lattice3('#skF_2', '#skF_3', A_40) | ~r1_lattice3(k3_lattice3('#skF_2'), A_40, '#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_155, c_181])).
% 2.13/1.24  tff(c_196, plain, (![A_44]: (r3_lattice3('#skF_2', '#skF_3', A_44) | ~r1_lattice3(k3_lattice3('#skF_2'), A_44, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_18, c_183])).
% 2.13/1.24  tff(c_199, plain, (r3_lattice3('#skF_2', '#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_118, c_196])).
% 2.13/1.24  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_199])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 33
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 3
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 0
% 2.13/1.24  #Demod        : 40
% 2.13/1.24  #Tautology    : 16
% 2.13/1.24  #SimpNegUnit  : 15
% 2.13/1.24  #BackRed      : 2
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.29
% 2.13/1.24  Parsing              : 0.16
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.18
% 2.13/1.24  Inferencing          : 0.07
% 2.13/1.24  Reduction            : 0.05
% 2.13/1.24  Demodulation         : 0.03
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.03
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.50
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
