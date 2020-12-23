%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   49 (  79 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 138 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xxreal_0 > v1_xreal_0 > v1_xcmplx_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_xreal_0,type,(
    v1_xreal_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_xcmplx_0,type,(
    v1_xcmplx_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xxreal_0,type,(
    v1_xxreal_0: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ? [A] :
      ( v1_xboole_0(A)
      & v1_xcmplx_0(A)
      & v1_xxreal_0(A)
      & v1_xreal_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_xreal_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_57,axiom,(
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

tff(f_71,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_14,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_93,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_hidden('#skF_3'(A_49,B_50,C_51),B_50)
      | r1_lattice3(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [B_52,A_53,C_54] :
      ( ~ v1_xboole_0(B_52)
      | r1_lattice3(A_53,B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_100,plain,(
    ! [B_52] :
      ( ~ v1_xboole_0(B_52)
      | r1_lattice3('#skF_5',B_52,'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_104,plain,(
    ! [B_55] :
      ( ~ v1_xboole_0(B_55)
      | r1_lattice3('#skF_5',B_55,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_61,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden('#skF_4'(A_36,B_37,C_38),B_37)
      | r2_lattice3(A_36,B_37,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_36))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ! [B_39,A_40,C_41] :
      ( ~ v1_xboole_0(B_39)
      | r2_lattice3(A_40,B_39,C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_40))
      | ~ l1_orders_2(A_40) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_68,plain,(
    ! [B_39] :
      ( ~ v1_xboole_0(B_39)
      | r2_lattice3('#skF_5',B_39,'#skF_6')
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_66])).

tff(c_77,plain,(
    ! [B_45] :
      ( ~ v1_xboole_0(B_45)
      | r2_lattice3('#skF_5',B_45,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_37,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_37])).

tff(c_32,plain,
    ( ~ r1_lattice3('#skF_5',k1_xboole_0,'#skF_6')
    | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,
    ( ~ r1_lattice3('#skF_5','#skF_2','#skF_6')
    | ~ r2_lattice3('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_32])).

tff(c_54,plain,(
    ~ r2_lattice3('#skF_5','#skF_2','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_54])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_85,plain,(
    ~ r1_lattice3('#skF_5','#skF_2','#skF_6') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_107,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_85])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.23  
% 1.67/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.23  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_xxreal_0 > v1_xreal_0 > v1_xcmplx_0 > v1_xboole_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.77/1.23  
% 1.77/1.23  %Foreground sorts:
% 1.77/1.23  
% 1.77/1.23  
% 1.77/1.23  %Background operators:
% 1.77/1.23  
% 1.77/1.23  
% 1.77/1.23  %Foreground operators:
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.77/1.23  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.77/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.77/1.23  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.77/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.77/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.77/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.23  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.77/1.23  tff(v1_xreal_0, type, v1_xreal_0: $i > $o).
% 1.77/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.77/1.23  tff(v1_xcmplx_0, type, v1_xcmplx_0: $i > $o).
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.77/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.77/1.23  tff(v1_xxreal_0, type, v1_xxreal_0: $i > $o).
% 1.77/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.23  
% 1.78/1.24  tff(f_43, axiom, (?[A]: (((v1_xboole_0(A) & v1_xcmplx_0(A)) & v1_xxreal_0(A)) & v1_xreal_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_xreal_0)).
% 1.78/1.24  tff(f_81, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.78/1.24  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.78/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.78/1.24  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.78/1.24  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.78/1.24  tff(c_14, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.24  tff(c_36, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.78/1.24  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.78/1.24  tff(c_93, plain, (![A_49, B_50, C_51]: (r2_hidden('#skF_3'(A_49, B_50, C_51), B_50) | r1_lattice3(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.78/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.24  tff(c_98, plain, (![B_52, A_53, C_54]: (~v1_xboole_0(B_52) | r1_lattice3(A_53, B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_53)) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_93, c_2])).
% 1.78/1.24  tff(c_100, plain, (![B_52]: (~v1_xboole_0(B_52) | r1_lattice3('#skF_5', B_52, '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_98])).
% 1.78/1.24  tff(c_104, plain, (![B_55]: (~v1_xboole_0(B_55) | r1_lattice3('#skF_5', B_55, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100])).
% 1.78/1.24  tff(c_61, plain, (![A_36, B_37, C_38]: (r2_hidden('#skF_4'(A_36, B_37, C_38), B_37) | r2_lattice3(A_36, B_37, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_36)) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.78/1.24  tff(c_66, plain, (![B_39, A_40, C_41]: (~v1_xboole_0(B_39) | r2_lattice3(A_40, B_39, C_41) | ~m1_subset_1(C_41, u1_struct_0(A_40)) | ~l1_orders_2(A_40))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.78/1.24  tff(c_68, plain, (![B_39]: (~v1_xboole_0(B_39) | r2_lattice3('#skF_5', B_39, '#skF_6') | ~l1_orders_2('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_66])).
% 1.78/1.24  tff(c_77, plain, (![B_45]: (~v1_xboole_0(B_45) | r2_lattice3('#skF_5', B_45, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 1.78/1.24  tff(c_37, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.24  tff(c_41, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_14, c_37])).
% 1.78/1.24  tff(c_32, plain, (~r1_lattice3('#skF_5', k1_xboole_0, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.78/1.24  tff(c_53, plain, (~r1_lattice3('#skF_5', '#skF_2', '#skF_6') | ~r2_lattice3('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_32])).
% 1.78/1.24  tff(c_54, plain, (~r2_lattice3('#skF_5', '#skF_2', '#skF_6')), inference(splitLeft, [status(thm)], [c_53])).
% 1.78/1.24  tff(c_80, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_77, c_54])).
% 1.78/1.24  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_80])).
% 1.78/1.24  tff(c_85, plain, (~r1_lattice3('#skF_5', '#skF_2', '#skF_6')), inference(splitRight, [status(thm)], [c_53])).
% 1.78/1.24  tff(c_107, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_104, c_85])).
% 1.78/1.24  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_107])).
% 1.78/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.24  
% 1.78/1.24  Inference rules
% 1.78/1.24  ----------------------
% 1.78/1.24  #Ref     : 0
% 1.78/1.24  #Sup     : 13
% 1.78/1.24  #Fact    : 0
% 1.78/1.24  #Define  : 0
% 1.78/1.24  #Split   : 1
% 1.78/1.24  #Chain   : 0
% 1.78/1.24  #Close   : 0
% 1.78/1.24  
% 1.78/1.24  Ordering : KBO
% 1.78/1.24  
% 1.78/1.24  Simplification rules
% 1.78/1.24  ----------------------
% 1.78/1.24  #Subsume      : 0
% 1.78/1.24  #Demod        : 7
% 1.78/1.24  #Tautology    : 5
% 1.78/1.24  #SimpNegUnit  : 0
% 1.78/1.24  #BackRed      : 1
% 1.78/1.24  
% 1.78/1.24  #Partial instantiations: 0
% 1.78/1.24  #Strategies tried      : 1
% 1.78/1.24  
% 1.78/1.24  Timing (in seconds)
% 1.78/1.24  ----------------------
% 1.78/1.24  Preprocessing        : 0.25
% 1.78/1.24  Parsing              : 0.13
% 1.78/1.24  CNF conversion       : 0.02
% 1.78/1.24  Main loop            : 0.13
% 1.78/1.24  Inferencing          : 0.06
% 1.78/1.24  Reduction            : 0.03
% 1.78/1.24  Demodulation         : 0.03
% 1.78/1.24  BG Simplification    : 0.01
% 1.78/1.24  Subsumption          : 0.02
% 1.78/1.24  Abstraction          : 0.01
% 1.78/1.24  MUC search           : 0.00
% 1.78/1.24  Cooper               : 0.00
% 1.78/1.24  Total                : 0.40
% 1.78/1.24  Index Insertion      : 0.00
% 1.78/1.24  Index Deletion       : 0.00
% 1.78/1.24  Index Matching       : 0.00
% 1.78/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
