%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   46 (  66 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 104 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > np__0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(np__0,type,(
    np__0: $i )).

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

tff(f_36,axiom,(
    v1_xboole_0(np__0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc0_boole)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_50,axiom,(
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
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
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

tff(c_8,plain,(
    v1_xboole_0(np__0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    np__0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_8])).

tff(c_30,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_2'(A_49,B_50,C_51),B_50)
      | r1_lattice3(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [B_55,A_56,C_57] :
      ( ~ v1_xboole_0(B_55)
      | r1_lattice3(A_56,B_55,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_94,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(B_55)
      | r1_lattice3('#skF_4',B_55,'#skF_5')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_98,plain,(
    ! [B_58] :
      ( ~ v1_xboole_0(B_58)
      | r1_lattice3('#skF_4',B_58,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_94])).

tff(c_53,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_3'(A_35,B_36,C_37),B_36)
      | r2_lattice3(A_35,B_36,C_37)
      | ~ m1_subset_1(C_37,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    ! [B_38,A_39,C_40] :
      ( ~ v1_xboole_0(B_38)
      | r2_lattice3(A_39,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_60,plain,(
    ! [B_38] :
      ( ~ v1_xboole_0(B_38)
      | r2_lattice3('#skF_4',B_38,'#skF_5')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_64,plain,(
    ! [B_41] :
      ( ~ v1_xboole_0(B_41)
      | r2_lattice3('#skF_4',B_41,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_60])).

tff(c_26,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_67,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_52])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_67])).

tff(c_72,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_101,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_98,c_72])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > np__0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.14  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.69/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.14  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.69/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.69/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.69/1.14  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.69/1.14  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.69/1.14  tff(np__0, type, np__0: $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.69/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.14  
% 1.69/1.15  tff(f_36, axiom, v1_xboole_0(np__0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', spc0_boole)).
% 1.69/1.15  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.69/1.15  tff(f_74, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.69/1.15  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 1.69/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.69/1.15  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 1.69/1.15  tff(c_8, plain, (v1_xboole_0(np__0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.69/1.15  tff(c_31, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.15  tff(c_35, plain, (np__0=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.69/1.15  tff(c_36, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35, c_8])).
% 1.69/1.15  tff(c_30, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.69/1.15  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.69/1.15  tff(c_86, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_2'(A_49, B_50, C_51), B_50) | r1_lattice3(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.69/1.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.15  tff(c_92, plain, (![B_55, A_56, C_57]: (~v1_xboole_0(B_55) | r1_lattice3(A_56, B_55, C_57) | ~m1_subset_1(C_57, u1_struct_0(A_56)) | ~l1_orders_2(A_56))), inference(resolution, [status(thm)], [c_86, c_2])).
% 1.69/1.15  tff(c_94, plain, (![B_55]: (~v1_xboole_0(B_55) | r1_lattice3('#skF_4', B_55, '#skF_5') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_92])).
% 1.69/1.15  tff(c_98, plain, (![B_58]: (~v1_xboole_0(B_58) | r1_lattice3('#skF_4', B_58, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_94])).
% 1.69/1.15  tff(c_53, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_3'(A_35, B_36, C_37), B_36) | r2_lattice3(A_35, B_36, C_37) | ~m1_subset_1(C_37, u1_struct_0(A_35)) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.69/1.15  tff(c_58, plain, (![B_38, A_39, C_40]: (~v1_xboole_0(B_38) | r2_lattice3(A_39, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(resolution, [status(thm)], [c_53, c_2])).
% 1.69/1.15  tff(c_60, plain, (![B_38]: (~v1_xboole_0(B_38) | r2_lattice3('#skF_4', B_38, '#skF_5') | ~l1_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_58])).
% 1.69/1.15  tff(c_64, plain, (![B_41]: (~v1_xboole_0(B_41) | r2_lattice3('#skF_4', B_41, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_60])).
% 1.69/1.15  tff(c_26, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.69/1.15  tff(c_52, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 1.69/1.15  tff(c_67, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_52])).
% 1.69/1.15  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_67])).
% 1.69/1.15  tff(c_72, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 1.69/1.15  tff(c_101, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_72])).
% 1.69/1.15  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_101])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 0
% 1.69/1.15  #Sup     : 13
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 1
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 0
% 1.69/1.15  #Demod        : 6
% 1.69/1.15  #Tautology    : 4
% 1.69/1.15  #SimpNegUnit  : 0
% 1.69/1.15  #BackRed      : 1
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.15  Timing (in seconds)
% 1.69/1.15  ----------------------
% 1.69/1.15  Preprocessing        : 0.27
% 1.69/1.15  Parsing              : 0.15
% 1.69/1.15  CNF conversion       : 0.02
% 1.69/1.15  Main loop            : 0.12
% 1.69/1.15  Inferencing          : 0.06
% 1.69/1.15  Reduction            : 0.03
% 1.69/1.15  Demodulation         : 0.02
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.02
% 1.69/1.15  Abstraction          : 0.00
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.42
% 1.69/1.15  Index Insertion      : 0.00
% 1.69/1.15  Index Deletion       : 0.00
% 1.69/1.15  Index Matching       : 0.00
% 1.69/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
