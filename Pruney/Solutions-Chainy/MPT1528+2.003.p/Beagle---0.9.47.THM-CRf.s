%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  88 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden('#skF_2'(A_40,B_41,C_42),B_41)
      | r1_lattice3(A_40,B_41,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_43,A_44,C_45] :
      ( ~ v1_xboole_0(B_43)
      | r1_lattice3(A_44,B_43,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_44))
      | ~ l1_orders_2(A_44) ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_64,plain,(
    ! [B_43] :
      ( ~ v1_xboole_0(B_43)
      | r1_lattice3('#skF_4',B_43,'#skF_5')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_68,plain,(
    ! [B_46] :
      ( ~ v1_xboole_0(B_46)
      | r1_lattice3('#skF_4',B_46,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_64])).

tff(c_36,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_3'(A_33,B_34,C_35),B_34)
      | r2_lattice3(A_33,B_34,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_33))
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_41,plain,(
    ! [B_36,A_37,C_38] :
      ( ~ v1_xboole_0(B_36)
      | r2_lattice3(A_37,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_43,plain,(
    ! [B_36] :
      ( ~ v1_xboole_0(B_36)
      | r2_lattice3('#skF_4',B_36,'#skF_5')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_47,plain,(
    ! [B_39] :
      ( ~ v1_xboole_0(B_39)
      | r2_lattice3('#skF_4',B_39,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_24,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_50,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_47,c_35])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_55,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_71,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_55])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  
% 1.82/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.26  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.82/1.26  
% 1.82/1.26  %Foreground sorts:
% 1.82/1.26  
% 1.82/1.26  
% 1.82/1.26  %Background operators:
% 1.82/1.26  
% 1.82/1.26  
% 1.82/1.26  %Foreground operators:
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.26  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.82/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.26  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.82/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.26  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.82/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.82/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.26  
% 1.82/1.28  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.82/1.28  tff(f_70, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.82/1.28  tff(f_46, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.82/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.82/1.28  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.82/1.28  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.28  tff(c_28, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.82/1.28  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.82/1.28  tff(c_57, plain, (![A_40, B_41, C_42]: (r2_hidden('#skF_2'(A_40, B_41, C_42), B_41) | r1_lattice3(A_40, B_41, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_40)) | ~l1_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.28  tff(c_62, plain, (![B_43, A_44, C_45]: (~v1_xboole_0(B_43) | r1_lattice3(A_44, B_43, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_44)) | ~l1_orders_2(A_44))), inference(resolution, [status(thm)], [c_57, c_2])).
% 1.82/1.28  tff(c_64, plain, (![B_43]: (~v1_xboole_0(B_43) | r1_lattice3('#skF_4', B_43, '#skF_5') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_62])).
% 1.82/1.28  tff(c_68, plain, (![B_46]: (~v1_xboole_0(B_46) | r1_lattice3('#skF_4', B_46, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_64])).
% 1.82/1.28  tff(c_36, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_3'(A_33, B_34, C_35), B_34) | r2_lattice3(A_33, B_34, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_33)) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.28  tff(c_41, plain, (![B_36, A_37, C_38]: (~v1_xboole_0(B_36) | r2_lattice3(A_37, B_36, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.82/1.28  tff(c_43, plain, (![B_36]: (~v1_xboole_0(B_36) | r2_lattice3('#skF_4', B_36, '#skF_5') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_41])).
% 1.82/1.28  tff(c_47, plain, (![B_39]: (~v1_xboole_0(B_39) | r2_lattice3('#skF_4', B_39, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_43])).
% 1.82/1.28  tff(c_24, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.82/1.28  tff(c_35, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_24])).
% 1.82/1.28  tff(c_50, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_47, c_35])).
% 1.82/1.28  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 1.82/1.28  tff(c_55, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 1.82/1.28  tff(c_71, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_55])).
% 1.82/1.28  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_71])).
% 1.82/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.28  
% 1.82/1.28  Inference rules
% 1.82/1.28  ----------------------
% 1.82/1.28  #Ref     : 0
% 1.82/1.28  #Sup     : 7
% 1.82/1.28  #Fact    : 0
% 1.82/1.28  #Define  : 0
% 1.82/1.28  #Split   : 1
% 1.82/1.28  #Chain   : 0
% 1.82/1.28  #Close   : 0
% 1.82/1.28  
% 1.82/1.28  Ordering : KBO
% 1.82/1.28  
% 1.82/1.28  Simplification rules
% 1.82/1.28  ----------------------
% 1.82/1.28  #Subsume      : 0
% 1.82/1.28  #Demod        : 4
% 1.82/1.28  #Tautology    : 1
% 1.82/1.28  #SimpNegUnit  : 0
% 1.82/1.28  #BackRed      : 0
% 1.82/1.28  
% 1.82/1.28  #Partial instantiations: 0
% 1.82/1.28  #Strategies tried      : 1
% 1.82/1.28  
% 1.82/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.28  Preprocessing        : 0.31
% 2.02/1.28  Parsing              : 0.17
% 2.02/1.28  CNF conversion       : 0.02
% 2.02/1.28  Main loop            : 0.14
% 2.02/1.28  Inferencing          : 0.06
% 2.02/1.28  Reduction            : 0.03
% 2.02/1.28  Demodulation         : 0.03
% 2.02/1.28  BG Simplification    : 0.02
% 2.02/1.28  Subsumption          : 0.02
% 2.02/1.28  Abstraction          : 0.01
% 2.02/1.28  MUC search           : 0.00
% 2.02/1.28  Cooper               : 0.00
% 2.02/1.28  Total                : 0.49
% 2.02/1.28  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
