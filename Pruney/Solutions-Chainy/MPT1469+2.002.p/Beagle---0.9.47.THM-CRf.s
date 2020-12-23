%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:38 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 184 expanded)
%              Number of equality atoms :   22 (  25 expanded)
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
       => ! [C] :
            ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
           => ( r1_lattices(k1_lattice3(A),B,C)
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,u1_struct_0(k1_lattice3(A)))
     => ! [C] :
          ( m1_subset_1(C,u1_struct_0(k1_lattice3(A)))
         => ( k1_lattices(k1_lattice3(A),B,C) = k2_xboole_0(B,C)
            & k2_lattices(k1_lattice3(A),B,C) = k3_xboole_0(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_lattice3)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ v2_struct_0(k1_lattice3(A))
      & v3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_lattices(k1_lattice3(A))
      & l3_lattices(k1_lattice3(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

tff(f_52,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_46,axiom,(
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
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_59,plain,(
    ~ r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_36])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_lattices(k1_lattice3(A_31),B_32,C_33) = k2_xboole_0(B_32,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0(k1_lattice3(A_31)))
      | ~ m1_subset_1(B_32,u1_struct_0(k1_lattice3(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_122,plain,(
    ! [B_37] :
      ( k1_lattices(k1_lattice3('#skF_1'),B_37,'#skF_3') = k2_xboole_0(B_37,'#skF_3')
      | ~ m1_subset_1(B_37,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_125,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_130,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_125])).

tff(c_18,plain,(
    ! [A_14] : ~ v2_struct_0(k1_lattice3(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_13] : l3_lattices(k1_lattice3(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_25] :
      ( l2_lattices(A_25)
      | ~ l3_lattices(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_51,plain,(
    ! [A_13] : l2_lattices(k1_lattice3(A_13)) ),
    inference(resolution,[status(thm)],[c_16,c_47])).

tff(c_156,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_lattices(A_42,B_43,C_44)
      | k1_lattices(A_42,B_43,C_44) != C_44
      | ~ m1_subset_1(C_44,u1_struct_0(A_42))
      | ~ m1_subset_1(B_43,u1_struct_0(A_42))
      | ~ l2_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_160,plain,(
    ! [B_43] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_43,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_43,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_43,u1_struct_0(k1_lattice3('#skF_1')))
      | ~ l2_lattices(k1_lattice3('#skF_1'))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_167,plain,(
    ! [B_43] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_43,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_43,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_43,u1_struct_0(k1_lattice3('#skF_1')))
      | v2_struct_0(k1_lattice3('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_160])).

tff(c_208,plain,(
    ! [B_50] :
      ( r1_lattices(k1_lattice3('#skF_1'),B_50,'#skF_3')
      | k1_lattices(k1_lattice3('#skF_1'),B_50,'#skF_3') != '#skF_3'
      | ~ m1_subset_1(B_50,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_167])).

tff(c_211,plain,
    ( r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3')
    | k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_208])).

tff(c_217,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_211])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_217])).

tff(c_220,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_245,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_lattices(k1_lattice3(A_53),B_54,C_55) = k2_xboole_0(B_54,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(k1_lattice3(A_53)))
      | ~ m1_subset_1(B_54,u1_struct_0(k1_lattice3(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_276,plain,(
    ! [B_60] :
      ( k1_lattices(k1_lattice3('#skF_1'),B_60,'#skF_3') = k2_xboole_0(B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0(k1_lattice3('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_245])).

tff(c_283,plain,(
    k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_276])).

tff(c_222,plain,(
    r1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_36])).

tff(c_365,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_lattices(A_68,B_69,C_70) = C_70
      | ~ r1_lattices(A_68,B_69,C_70)
      | ~ m1_subset_1(C_70,u1_struct_0(A_68))
      | ~ m1_subset_1(B_69,u1_struct_0(A_68))
      | ~ l2_lattices(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_367,plain,
    ( k1_lattices(k1_lattice3('#skF_1'),'#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0(k1_lattice3('#skF_1')))
    | ~ l2_lattices(k1_lattice3('#skF_1'))
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(resolution,[status(thm)],[c_222,c_365])).

tff(c_370,plain,
    ( k2_xboole_0('#skF_2','#skF_3') = '#skF_3'
    | v2_struct_0(k1_lattice3('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28,c_26,c_283,c_367])).

tff(c_371,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_370])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_379,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_4])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:56:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.34  %$ r1_lattices > r1_tarski > m1_subset_1 > v3_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_lattice3 > #skF_2 > #skF_3 > #skF_1
% 2.32/1.34  
% 2.32/1.34  %Foreground sorts:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Background operators:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Foreground operators:
% 2.32/1.34  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.32/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.34  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.32/1.34  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.34  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.32/1.34  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.32/1.34  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.32/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.34  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.34  tff(v3_lattices, type, v3_lattices: $i > $o).
% 2.32/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.32/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.34  
% 2.32/1.37  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => (r1_lattices(k1_lattice3(A), B, C) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_lattice3)).
% 2.32/1.37  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.32/1.37  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, u1_struct_0(k1_lattice3(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k1_lattice3(A))) => ((k1_lattices(k1_lattice3(A), B, C) = k2_xboole_0(B, C)) & (k2_lattices(k1_lattice3(A), B, C) = k3_xboole_0(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_lattice3)).
% 2.32/1.37  tff(f_61, axiom, (![A]: (~v2_struct_0(k1_lattice3(A)) & v3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_lattice3)).
% 2.32/1.37  tff(f_56, axiom, (![A]: (v3_lattices(k1_lattice3(A)) & l3_lattices(k1_lattice3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 2.32/1.37  tff(f_52, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.32/1.37  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.32/1.37  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.32/1.37  tff(c_30, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.37  tff(c_59, plain, (~r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.32/1.37  tff(c_36, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.37  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_59, c_36])).
% 2.32/1.37  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.32/1.37  tff(c_64, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_60, c_2])).
% 2.32/1.37  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.37  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.32/1.37  tff(c_73, plain, (![A_31, B_32, C_33]: (k1_lattices(k1_lattice3(A_31), B_32, C_33)=k2_xboole_0(B_32, C_33) | ~m1_subset_1(C_33, u1_struct_0(k1_lattice3(A_31))) | ~m1_subset_1(B_32, u1_struct_0(k1_lattice3(A_31))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.32/1.37  tff(c_122, plain, (![B_37]: (k1_lattices(k1_lattice3('#skF_1'), B_37, '#skF_3')=k2_xboole_0(B_37, '#skF_3') | ~m1_subset_1(B_37, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_73])).
% 2.32/1.37  tff(c_125, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_122])).
% 2.32/1.37  tff(c_130, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_125])).
% 2.32/1.37  tff(c_18, plain, (![A_14]: (~v2_struct_0(k1_lattice3(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.32/1.37  tff(c_16, plain, (![A_13]: (l3_lattices(k1_lattice3(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.32/1.37  tff(c_47, plain, (![A_25]: (l2_lattices(A_25) | ~l3_lattices(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.32/1.37  tff(c_51, plain, (![A_13]: (l2_lattices(k1_lattice3(A_13)))), inference(resolution, [status(thm)], [c_16, c_47])).
% 2.32/1.37  tff(c_156, plain, (![A_42, B_43, C_44]: (r1_lattices(A_42, B_43, C_44) | k1_lattices(A_42, B_43, C_44)!=C_44 | ~m1_subset_1(C_44, u1_struct_0(A_42)) | ~m1_subset_1(B_43, u1_struct_0(A_42)) | ~l2_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.37  tff(c_160, plain, (![B_43]: (r1_lattices(k1_lattice3('#skF_1'), B_43, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_43, '#skF_3')!='#skF_3' | ~m1_subset_1(B_43, u1_struct_0(k1_lattice3('#skF_1'))) | ~l2_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_156])).
% 2.32/1.37  tff(c_167, plain, (![B_43]: (r1_lattices(k1_lattice3('#skF_1'), B_43, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_43, '#skF_3')!='#skF_3' | ~m1_subset_1(B_43, u1_struct_0(k1_lattice3('#skF_1'))) | v2_struct_0(k1_lattice3('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_160])).
% 2.32/1.37  tff(c_208, plain, (![B_50]: (r1_lattices(k1_lattice3('#skF_1'), B_50, '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), B_50, '#skF_3')!='#skF_3' | ~m1_subset_1(B_50, u1_struct_0(k1_lattice3('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_18, c_167])).
% 2.32/1.37  tff(c_211, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3') | k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_28, c_208])).
% 2.32/1.37  tff(c_217, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_211])).
% 2.32/1.37  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_217])).
% 2.32/1.37  tff(c_220, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.32/1.37  tff(c_245, plain, (![A_53, B_54, C_55]: (k1_lattices(k1_lattice3(A_53), B_54, C_55)=k2_xboole_0(B_54, C_55) | ~m1_subset_1(C_55, u1_struct_0(k1_lattice3(A_53))) | ~m1_subset_1(B_54, u1_struct_0(k1_lattice3(A_53))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.32/1.37  tff(c_276, plain, (![B_60]: (k1_lattices(k1_lattice3('#skF_1'), B_60, '#skF_3')=k2_xboole_0(B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0(k1_lattice3('#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_245])).
% 2.32/1.37  tff(c_283, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_276])).
% 2.32/1.37  tff(c_222, plain, (r1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_220, c_36])).
% 2.32/1.37  tff(c_365, plain, (![A_68, B_69, C_70]: (k1_lattices(A_68, B_69, C_70)=C_70 | ~r1_lattices(A_68, B_69, C_70) | ~m1_subset_1(C_70, u1_struct_0(A_68)) | ~m1_subset_1(B_69, u1_struct_0(A_68)) | ~l2_lattices(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.37  tff(c_367, plain, (k1_lattices(k1_lattice3('#skF_1'), '#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', u1_struct_0(k1_lattice3('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0(k1_lattice3('#skF_1'))) | ~l2_lattices(k1_lattice3('#skF_1')) | v2_struct_0(k1_lattice3('#skF_1'))), inference(resolution, [status(thm)], [c_222, c_365])).
% 2.32/1.37  tff(c_370, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3' | v2_struct_0(k1_lattice3('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28, c_26, c_283, c_367])).
% 2.32/1.37  tff(c_371, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_18, c_370])).
% 2.32/1.37  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.37  tff(c_379, plain, (r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_371, c_4])).
% 2.32/1.37  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_379])).
% 2.32/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  
% 2.32/1.37  Inference rules
% 2.32/1.37  ----------------------
% 2.32/1.37  #Ref     : 0
% 2.32/1.37  #Sup     : 91
% 2.32/1.37  #Fact    : 0
% 2.32/1.37  #Define  : 0
% 2.32/1.37  #Split   : 6
% 2.32/1.37  #Chain   : 0
% 2.32/1.37  #Close   : 0
% 2.32/1.37  
% 2.32/1.37  Ordering : KBO
% 2.32/1.37  
% 2.32/1.37  Simplification rules
% 2.32/1.37  ----------------------
% 2.32/1.37  #Subsume      : 0
% 2.32/1.37  #Demod        : 35
% 2.32/1.37  #Tautology    : 53
% 2.32/1.37  #SimpNegUnit  : 9
% 2.32/1.37  #BackRed      : 1
% 2.32/1.37  
% 2.32/1.37  #Partial instantiations: 0
% 2.32/1.37  #Strategies tried      : 1
% 2.32/1.37  
% 2.32/1.37  Timing (in seconds)
% 2.32/1.37  ----------------------
% 2.32/1.37  Preprocessing        : 0.29
% 2.32/1.37  Parsing              : 0.17
% 2.32/1.37  CNF conversion       : 0.02
% 2.32/1.37  Main loop            : 0.24
% 2.32/1.37  Inferencing          : 0.09
% 2.32/1.37  Reduction            : 0.08
% 2.32/1.38  Demodulation         : 0.05
% 2.32/1.38  BG Simplification    : 0.01
% 2.32/1.38  Subsumption          : 0.04
% 2.32/1.38  Abstraction          : 0.01
% 2.32/1.38  MUC search           : 0.00
% 2.32/1.38  Cooper               : 0.00
% 2.32/1.38  Total                : 0.58
% 2.32/1.38  Index Insertion      : 0.00
% 2.32/1.38  Index Deletion       : 0.00
% 2.32/1.38  Index Matching       : 0.00
% 2.32/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
