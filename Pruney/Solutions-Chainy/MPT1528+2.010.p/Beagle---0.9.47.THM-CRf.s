%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  82 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_62,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
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

tff(c_26,plain,
    ( ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_72,plain,(
    ~ r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_86,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden('#skF_2'(A_42,B_43,C_44),B_43)
      | r2_lattice3(A_42,B_43,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_92,plain,(
    ! [A_45,C_46] :
      ( r2_lattice3(A_45,k1_xboole_0,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45) ) ),
    inference(resolution,[status(thm)],[c_86,c_56])).

tff(c_95,plain,
    ( r2_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_98,plain,(
    r2_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_98])).

tff(c_101,plain,(
    ~ r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_116,plain,(
    ! [A_52,B_53,C_54] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_54),B_53)
      | r1_lattice3(A_52,B_53,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_52))
      | ~ l1_orders_2(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ! [A_55,C_56] :
      ( r1_lattice3(A_55,k1_xboole_0,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(resolution,[status(thm)],[c_116,c_56])).

tff(c_125,plain,
    ( r1_lattice3('#skF_3',k1_xboole_0,'#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_128,plain,(
    r1_lattice3('#skF_3',k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.82/1.15  
% 1.82/1.15  %Foreground sorts:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Background operators:
% 1.82/1.15  
% 1.82/1.15  
% 1.82/1.15  %Foreground operators:
% 1.82/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.15  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.82/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.15  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.82/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.15  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.82/1.15  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.15  
% 1.82/1.16  tff(f_72, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.82/1.16  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.82/1.16  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.82/1.16  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.82/1.16  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.82/1.16  tff(c_26, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.82/1.16  tff(c_72, plain, (~r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 1.82/1.16  tff(c_30, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.82/1.16  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.82/1.16  tff(c_86, plain, (![A_42, B_43, C_44]: (r2_hidden('#skF_2'(A_42, B_43, C_44), B_43) | r2_lattice3(A_42, B_43, C_44) | ~m1_subset_1(C_44, u1_struct_0(A_42)) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.16  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.16  tff(c_53, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.82/1.16  tff(c_56, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.82/1.16  tff(c_92, plain, (![A_45, C_46]: (r2_lattice3(A_45, k1_xboole_0, C_46) | ~m1_subset_1(C_46, u1_struct_0(A_45)) | ~l1_orders_2(A_45))), inference(resolution, [status(thm)], [c_86, c_56])).
% 1.82/1.16  tff(c_95, plain, (r2_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_92])).
% 1.82/1.16  tff(c_98, plain, (r2_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_95])).
% 1.82/1.16  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_98])).
% 1.82/1.16  tff(c_101, plain, (~r1_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 1.82/1.16  tff(c_116, plain, (![A_52, B_53, C_54]: (r2_hidden('#skF_1'(A_52, B_53, C_54), B_53) | r1_lattice3(A_52, B_53, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_52)) | ~l1_orders_2(A_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.16  tff(c_122, plain, (![A_55, C_56]: (r1_lattice3(A_55, k1_xboole_0, C_56) | ~m1_subset_1(C_56, u1_struct_0(A_55)) | ~l1_orders_2(A_55))), inference(resolution, [status(thm)], [c_116, c_56])).
% 1.82/1.16  tff(c_125, plain, (r1_lattice3('#skF_3', k1_xboole_0, '#skF_4') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_28, c_122])).
% 1.82/1.16  tff(c_128, plain, (r1_lattice3('#skF_3', k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125])).
% 1.82/1.16  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_128])).
% 1.82/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  Inference rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Ref     : 0
% 1.82/1.16  #Sup     : 18
% 1.82/1.16  #Fact    : 0
% 1.82/1.16  #Define  : 0
% 1.82/1.16  #Split   : 1
% 1.82/1.16  #Chain   : 0
% 1.82/1.16  #Close   : 0
% 1.82/1.16  
% 1.82/1.16  Ordering : KBO
% 1.82/1.16  
% 1.82/1.16  Simplification rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Subsume      : 1
% 1.82/1.16  #Demod        : 5
% 1.82/1.16  #Tautology    : 9
% 1.82/1.16  #SimpNegUnit  : 2
% 1.82/1.16  #BackRed      : 0
% 1.82/1.16  
% 1.82/1.16  #Partial instantiations: 0
% 1.82/1.16  #Strategies tried      : 1
% 1.82/1.16  
% 1.82/1.16  Timing (in seconds)
% 1.82/1.16  ----------------------
% 1.82/1.16  Preprocessing        : 0.28
% 1.82/1.16  Parsing              : 0.15
% 1.82/1.16  CNF conversion       : 0.02
% 1.82/1.16  Main loop            : 0.12
% 1.82/1.16  Inferencing          : 0.05
% 1.82/1.16  Reduction            : 0.03
% 1.82/1.16  Demodulation         : 0.02
% 1.82/1.16  BG Simplification    : 0.01
% 1.82/1.16  Subsumption          : 0.02
% 1.82/1.16  Abstraction          : 0.00
% 1.82/1.16  MUC search           : 0.00
% 1.82/1.16  Cooper               : 0.00
% 1.82/1.16  Total                : 0.43
% 1.82/1.16  Index Insertion      : 0.00
% 1.82/1.16  Index Deletion       : 0.00
% 1.82/1.16  Index Matching       : 0.00
% 1.82/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
