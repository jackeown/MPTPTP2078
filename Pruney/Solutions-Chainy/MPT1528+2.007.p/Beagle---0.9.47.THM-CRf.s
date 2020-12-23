%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
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
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_45,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_59,axiom,(
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

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_1'(A_37,B_38,C_39),B_38)
      | r1_lattice3(A_37,B_38,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_37))
      | ~ l1_orders_2(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [B_40,A_41,C_42] :
      ( ~ v1_xboole_0(B_40)
      | r1_lattice3(A_41,B_40,C_42)
      | ~ m1_subset_1(C_42,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_50,c_4])).

tff(c_57,plain,(
    ! [B_40] :
      ( ~ v1_xboole_0(B_40)
      | r1_lattice3('#skF_3',B_40,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_61,plain,(
    ! [B_43] :
      ( ~ v1_xboole_0(B_43)
      | r1_lattice3('#skF_3',B_43,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_57])).

tff(c_29,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_2'(A_30,B_31,C_32),B_31)
      | r2_lattice3(A_30,B_31,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [B_33,A_34,C_35] :
      ( ~ v1_xboole_0(B_33)
      | r2_lattice3(A_34,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_29,c_4])).

tff(c_36,plain,(
    ! [B_33] :
      ( ~ v1_xboole_0(B_33)
      | r2_lattice3('#skF_3',B_33,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_40,plain,(
    ! [B_36] :
      ( ~ v1_xboole_0(B_36)
      | r2_lattice3('#skF_3',B_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_22,plain,
    ( ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_43,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_28])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_48,plain,(
    ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_64,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_61,c_48])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:15:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  
% 1.69/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.12  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.69/1.12  
% 1.69/1.12  %Foreground sorts:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Background operators:
% 1.69/1.12  
% 1.69/1.12  
% 1.69/1.12  %Foreground operators:
% 1.69/1.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.12  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.69/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.12  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.69/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.69/1.12  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.69/1.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.69/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.12  
% 1.69/1.13  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.69/1.13  tff(f_69, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.69/1.13  tff(f_45, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 1.69/1.13  tff(f_31, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 1.69/1.13  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 1.69/1.13  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.69/1.13  tff(c_26, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.13  tff(c_24, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.13  tff(c_50, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_1'(A_37, B_38, C_39), B_38) | r1_lattice3(A_37, B_38, C_39) | ~m1_subset_1(C_39, u1_struct_0(A_37)) | ~l1_orders_2(A_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.69/1.13  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.13  tff(c_55, plain, (![B_40, A_41, C_42]: (~v1_xboole_0(B_40) | r1_lattice3(A_41, B_40, C_42) | ~m1_subset_1(C_42, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(resolution, [status(thm)], [c_50, c_4])).
% 1.69/1.13  tff(c_57, plain, (![B_40]: (~v1_xboole_0(B_40) | r1_lattice3('#skF_3', B_40, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_55])).
% 1.69/1.13  tff(c_61, plain, (![B_43]: (~v1_xboole_0(B_43) | r1_lattice3('#skF_3', B_43, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_57])).
% 1.69/1.13  tff(c_29, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_2'(A_30, B_31, C_32), B_31) | r2_lattice3(A_30, B_31, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.69/1.13  tff(c_34, plain, (![B_33, A_34, C_35]: (~v1_xboole_0(B_33) | r2_lattice3(A_34, B_33, C_35) | ~m1_subset_1(C_35, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_29, c_4])).
% 1.69/1.13  tff(c_36, plain, (![B_33]: (~v1_xboole_0(B_33) | r2_lattice3('#skF_3', B_33, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_34])).
% 1.69/1.13  tff(c_40, plain, (![B_36]: (~v1_xboole_0(B_36) | r2_lattice3('#skF_3', B_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 1.69/1.13  tff(c_22, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.13  tff(c_28, plain, (~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 1.69/1.13  tff(c_43, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_28])).
% 1.69/1.13  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_43])).
% 1.69/1.13  tff(c_48, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 1.69/1.13  tff(c_64, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_61, c_48])).
% 1.69/1.13  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_64])).
% 1.69/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  Inference rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Ref     : 0
% 1.69/1.13  #Sup     : 6
% 1.69/1.13  #Fact    : 0
% 1.69/1.13  #Define  : 0
% 1.69/1.13  #Split   : 1
% 1.69/1.13  #Chain   : 0
% 1.69/1.13  #Close   : 0
% 1.69/1.13  
% 1.69/1.13  Ordering : KBO
% 1.69/1.13  
% 1.69/1.13  Simplification rules
% 1.69/1.13  ----------------------
% 1.69/1.13  #Subsume      : 0
% 1.69/1.13  #Demod        : 4
% 1.69/1.13  #Tautology    : 0
% 1.69/1.13  #SimpNegUnit  : 0
% 1.69/1.13  #BackRed      : 0
% 1.69/1.13  
% 1.69/1.13  #Partial instantiations: 0
% 1.69/1.13  #Strategies tried      : 1
% 1.69/1.13  
% 1.69/1.13  Timing (in seconds)
% 1.69/1.13  ----------------------
% 1.69/1.13  Preprocessing        : 0.27
% 1.69/1.13  Parsing              : 0.15
% 1.69/1.13  CNF conversion       : 0.02
% 1.69/1.13  Main loop            : 0.10
% 1.69/1.13  Inferencing          : 0.04
% 1.69/1.13  Reduction            : 0.03
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.14  BG Simplification    : 0.01
% 1.69/1.14  Subsumption          : 0.01
% 1.69/1.14  Abstraction          : 0.00
% 1.69/1.14  MUC search           : 0.00
% 1.69/1.14  Cooper               : 0.00
% 1.69/1.14  Total                : 0.40
% 1.69/1.14  Index Insertion      : 0.00
% 1.69/1.14  Index Deletion       : 0.00
% 1.69/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
