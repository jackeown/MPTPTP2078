%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_22,plain,
    ( ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_2'(A_32,B_33,C_34),B_33)
      | r2_lattice3(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_tarski(B_3,A_2)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [B_38,A_39,C_40] :
      ( ~ r1_tarski(B_38,'#skF_2'(A_39,B_38,C_40))
      | r2_lattice3(A_39,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_30,c_4])).

tff(c_47,plain,(
    ! [A_44,C_45] :
      ( r2_lattice3(A_44,k1_xboole_0,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_53,plain,
    ( r2_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_57,plain,(
    r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_53])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_57])).

tff(c_60,plain,(
    ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_67,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_1'(A_49,B_50,C_51),B_50)
      | r1_lattice3(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [B_60,A_61,C_62] :
      ( ~ r1_tarski(B_60,'#skF_1'(A_61,B_60,C_62))
      | r1_lattice3(A_61,B_60,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_97,plain,(
    ! [A_66,C_67] :
      ( r1_lattice3(A_66,k1_xboole_0,C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_103,plain,
    ( r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_107,plain,(
    r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_103])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.16  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.64/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.16  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.16  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.64/1.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.64/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.16  
% 1.64/1.18  tff(f_70, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.64/1.18  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.64/1.18  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.64/1.18  tff(f_32, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.64/1.18  tff(f_46, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.64/1.18  tff(c_22, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.18  tff(c_29, plain, (~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 1.64/1.18  tff(c_26, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.18  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.18  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.18  tff(c_30, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_2'(A_32, B_33, C_34), B_33) | r2_lattice3(A_32, B_33, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.64/1.18  tff(c_4, plain, (![B_3, A_2]: (~r1_tarski(B_3, A_2) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.64/1.18  tff(c_40, plain, (![B_38, A_39, C_40]: (~r1_tarski(B_38, '#skF_2'(A_39, B_38, C_40)) | r2_lattice3(A_39, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(resolution, [status(thm)], [c_30, c_4])).
% 1.64/1.18  tff(c_47, plain, (![A_44, C_45]: (r2_lattice3(A_44, k1_xboole_0, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.64/1.18  tff(c_53, plain, (r2_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_47])).
% 1.64/1.18  tff(c_57, plain, (r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_53])).
% 1.64/1.18  tff(c_59, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_57])).
% 1.64/1.18  tff(c_60, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 1.64/1.18  tff(c_67, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_1'(A_49, B_50, C_51), B_50) | r1_lattice3(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.18  tff(c_90, plain, (![B_60, A_61, C_62]: (~r1_tarski(B_60, '#skF_1'(A_61, B_60, C_62)) | r1_lattice3(A_61, B_60, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_61)) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_67, c_4])).
% 1.64/1.18  tff(c_97, plain, (![A_66, C_67]: (r1_lattice3(A_66, k1_xboole_0, C_67) | ~m1_subset_1(C_67, u1_struct_0(A_66)) | ~l1_orders_2(A_66))), inference(resolution, [status(thm)], [c_2, c_90])).
% 1.64/1.18  tff(c_103, plain, (r1_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_24, c_97])).
% 1.64/1.18  tff(c_107, plain, (r1_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_103])).
% 1.64/1.18  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_107])).
% 1.64/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  Inference rules
% 1.64/1.18  ----------------------
% 1.64/1.18  #Ref     : 0
% 1.64/1.18  #Sup     : 13
% 1.64/1.18  #Fact    : 0
% 1.64/1.18  #Define  : 0
% 1.64/1.18  #Split   : 1
% 1.64/1.18  #Chain   : 0
% 1.64/1.18  #Close   : 0
% 1.64/1.18  
% 1.64/1.18  Ordering : KBO
% 1.64/1.18  
% 1.64/1.18  Simplification rules
% 1.64/1.18  ----------------------
% 1.64/1.18  #Subsume      : 0
% 1.64/1.18  #Demod        : 4
% 1.64/1.18  #Tautology    : 1
% 1.64/1.18  #SimpNegUnit  : 2
% 1.64/1.18  #BackRed      : 0
% 1.64/1.18  
% 1.64/1.18  #Partial instantiations: 0
% 1.64/1.18  #Strategies tried      : 1
% 1.64/1.18  
% 1.64/1.18  Timing (in seconds)
% 1.64/1.18  ----------------------
% 1.89/1.18  Preprocessing        : 0.28
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.14
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.03
% 1.89/1.18  Demodulation         : 0.02
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.02
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.44
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
