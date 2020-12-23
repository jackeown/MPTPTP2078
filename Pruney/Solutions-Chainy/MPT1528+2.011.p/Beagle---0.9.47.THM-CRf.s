%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:57 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  94 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

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

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

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

tff(c_26,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_30,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_3'(A_50,B_51,C_52),B_51)
      | r2_lattice3(A_50,B_51,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_43,plain,(
    ! [A_6,C_37] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_45,plain,(
    ! [C_37] : ~ r2_hidden(C_37,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_92,plain,(
    ! [A_53,C_54] :
      ( r2_lattice3(A_53,k1_xboole_0,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(A_53))
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_81,c_45])).

tff(c_95,plain,
    ( r2_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_98,plain,(
    r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_98])).

tff(c_101,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_144,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_2'(A_70,B_71,C_72),B_71)
      | r1_lattice3(A_70,B_71,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_103,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    ! [A_6,C_57] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_57,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_103])).

tff(c_108,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_155,plain,(
    ! [A_73,C_74] :
      ( r1_lattice3(A_73,k1_xboole_0,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(resolution,[status(thm)],[c_144,c_108])).

tff(c_158,plain,
    ( r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_155])).

tff(c_161,plain,(
    r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_158])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_xboole_0 > m1_subset_1 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.17  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 1.88/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.17  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 1.88/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.88/1.17  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 1.88/1.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.17  
% 1.88/1.18  tff(f_81, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 1.88/1.18  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 1.88/1.18  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.88/1.18  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.18  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.88/1.18  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 1.88/1.18  tff(c_26, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.18  tff(c_39, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 1.88/1.18  tff(c_30, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.18  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 1.88/1.18  tff(c_81, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_3'(A_50, B_51, C_52), B_51) | r2_lattice3(A_50, B_51, C_52) | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.88/1.18  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.18  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.18  tff(c_40, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.18  tff(c_43, plain, (![A_6, C_37]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_40])).
% 1.88/1.18  tff(c_45, plain, (![C_37]: (~r2_hidden(C_37, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 1.88/1.18  tff(c_92, plain, (![A_53, C_54]: (r2_lattice3(A_53, k1_xboole_0, C_54) | ~m1_subset_1(C_54, u1_struct_0(A_53)) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_81, c_45])).
% 1.88/1.18  tff(c_95, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_28, c_92])).
% 1.88/1.18  tff(c_98, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_95])).
% 1.88/1.18  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_98])).
% 1.88/1.18  tff(c_101, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 1.88/1.18  tff(c_144, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_2'(A_70, B_71, C_72), B_71) | r1_lattice3(A_70, B_71, C_72) | ~m1_subset_1(C_72, u1_struct_0(A_70)) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.18  tff(c_103, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.18  tff(c_106, plain, (![A_6, C_57]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_103])).
% 1.88/1.18  tff(c_108, plain, (![C_57]: (~r2_hidden(C_57, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_106])).
% 1.88/1.18  tff(c_155, plain, (![A_73, C_74]: (r1_lattice3(A_73, k1_xboole_0, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(resolution, [status(thm)], [c_144, c_108])).
% 1.88/1.18  tff(c_158, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_28, c_155])).
% 1.88/1.18  tff(c_161, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_158])).
% 1.88/1.18  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_161])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 22
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 1
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 2
% 1.88/1.18  #Demod        : 11
% 1.88/1.18  #Tautology    : 7
% 1.88/1.18  #SimpNegUnit  : 4
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.19  Preprocessing        : 0.28
% 1.88/1.19  Parsing              : 0.16
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.14
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.04
% 1.88/1.19  Demodulation         : 0.03
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.45
% 1.99/1.19  Index Insertion      : 0.00
% 1.99/1.19  Index Deletion       : 0.00
% 1.99/1.19  Index Matching       : 0.00
% 1.99/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
