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
% DateTime   : Thu Dec  3 10:24:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 106 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_orders_2 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_28,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_43,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_32,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_144,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_3'(A_49,B_50,C_51),B_50)
      | r2_lattice3(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_63,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k3_xboole_0(A_42,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_73,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_99,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_191,plain,(
    ! [A_53,C_54] :
      ( r2_lattice3(A_53,k1_xboole_0,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_144,c_99])).

tff(c_194,plain,
    ( r2_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_191])).

tff(c_197,plain,(
    r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_194])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_197])).

tff(c_200,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_402,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_2'(A_75,B_76,C_77),B_76)
      | r1_lattice3(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_221,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k3_xboole_0(A_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_231,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_6])).

tff(c_244,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_4])).

tff(c_248,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_244])).

tff(c_413,plain,(
    ! [A_78,C_79] :
      ( r1_lattice3(A_78,k1_xboole_0,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(resolution,[status(thm)],[c_402,c_248])).

tff(c_416,plain,
    ( r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_413])).

tff(c_419,plain,(
    r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_416])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_orders_2 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.10/1.28  
% 2.10/1.28  %Foreground sorts:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Background operators:
% 2.10/1.28  
% 2.10/1.28  
% 2.10/1.28  %Foreground operators:
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.10/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.28  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.10/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.28  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.10/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.28  
% 2.10/1.29  tff(f_83, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 2.10/1.29  tff(f_73, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 2.10/1.29  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.29  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.10/1.29  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.29  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.29  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 2.10/1.29  tff(c_28, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.29  tff(c_43, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 2.10/1.29  tff(c_32, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.29  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.29  tff(c_144, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_3'(A_49, B_50, C_51), B_50) | r2_lattice3(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.29  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.29  tff(c_6, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.29  tff(c_45, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.29  tff(c_63, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k3_xboole_0(A_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 2.10/1.29  tff(c_73, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_63, c_6])).
% 2.10/1.29  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.29  tff(c_94, plain, (![C_5]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 2.10/1.29  tff(c_99, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_94])).
% 2.10/1.29  tff(c_191, plain, (![A_53, C_54]: (r2_lattice3(A_53, k1_xboole_0, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_53)) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_144, c_99])).
% 2.10/1.29  tff(c_194, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_191])).
% 2.10/1.29  tff(c_197, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_194])).
% 2.10/1.29  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_197])).
% 2.10/1.29  tff(c_200, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 2.10/1.29  tff(c_402, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_2'(A_75, B_76, C_77), B_76) | r1_lattice3(A_75, B_76, C_77) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~l1_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.10/1.29  tff(c_203, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.29  tff(c_221, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k3_xboole_0(A_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_203])).
% 2.10/1.29  tff(c_231, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_221, c_6])).
% 2.10/1.29  tff(c_244, plain, (![C_5]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_231, c_4])).
% 2.10/1.29  tff(c_248, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_244])).
% 2.10/1.29  tff(c_413, plain, (![A_78, C_79]: (r1_lattice3(A_78, k1_xboole_0, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(resolution, [status(thm)], [c_402, c_248])).
% 2.10/1.29  tff(c_416, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_413])).
% 2.10/1.29  tff(c_419, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_416])).
% 2.10/1.29  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_200, c_419])).
% 2.10/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  Inference rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Ref     : 0
% 2.10/1.29  #Sup     : 90
% 2.10/1.29  #Fact    : 0
% 2.10/1.29  #Define  : 0
% 2.10/1.29  #Split   : 1
% 2.10/1.29  #Chain   : 0
% 2.10/1.29  #Close   : 0
% 2.10/1.29  
% 2.10/1.29  Ordering : KBO
% 2.10/1.29  
% 2.10/1.29  Simplification rules
% 2.10/1.29  ----------------------
% 2.10/1.29  #Subsume      : 0
% 2.10/1.29  #Demod        : 43
% 2.10/1.29  #Tautology    : 58
% 2.10/1.29  #SimpNegUnit  : 2
% 2.10/1.29  #BackRed      : 0
% 2.10/1.29  
% 2.10/1.29  #Partial instantiations: 0
% 2.10/1.29  #Strategies tried      : 1
% 2.10/1.29  
% 2.10/1.29  Timing (in seconds)
% 2.10/1.29  ----------------------
% 2.10/1.29  Preprocessing        : 0.28
% 2.10/1.29  Parsing              : 0.15
% 2.10/1.29  CNF conversion       : 0.02
% 2.10/1.29  Main loop            : 0.21
% 2.10/1.29  Inferencing          : 0.09
% 2.10/1.29  Reduction            : 0.06
% 2.10/1.29  Demodulation         : 0.05
% 2.10/1.29  BG Simplification    : 0.02
% 2.10/1.29  Subsumption          : 0.03
% 2.10/1.30  Abstraction          : 0.01
% 2.10/1.30  MUC search           : 0.00
% 2.10/1.30  Cooper               : 0.00
% 2.10/1.30  Total                : 0.52
% 2.10/1.30  Index Insertion      : 0.00
% 2.10/1.30  Index Deletion       : 0.00
% 2.10/1.30  Index Matching       : 0.00
% 2.10/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
