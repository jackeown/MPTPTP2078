%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 125 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_450,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_4'(A_123,B_124,C_125),B_124)
      | r2_hidden('#skF_5'(A_123,B_124,C_125),C_125)
      | k10_relat_1(A_123,B_124) = C_125
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [D_79,A_80,B_81] :
      ( ~ r2_hidden(D_79,'#skF_2'(A_80,B_81))
      | ~ r2_hidden(D_79,B_81)
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    ! [A_86,A_87,B_88] :
      ( ~ r2_hidden('#skF_1'(A_86,'#skF_2'(A_87,B_88)),B_88)
      | ~ r2_hidden(A_87,B_88)
      | r1_xboole_0(A_86,'#skF_2'(A_87,B_88)) ) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_135,plain,(
    ! [A_92,A_93] :
      ( ~ r2_hidden(A_92,A_93)
      | r1_xboole_0(A_93,'#skF_2'(A_92,A_93)) ) ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_94,A_95] :
      ( r1_xboole_0('#skF_2'(A_94,A_95),A_95)
      | ~ r2_hidden(A_94,A_95) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_62,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_2'(A_67,B_68),B_68)
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [B_60] :
      ( ~ r1_xboole_0(B_60,'#skF_7')
      | ~ r2_hidden(B_60,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    ! [A_67] :
      ( ~ r1_xboole_0('#skF_2'(A_67,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_40])).

tff(c_152,plain,(
    ! [A_94] : ~ r2_hidden(A_94,'#skF_7') ),
    inference(resolution,[status(thm)],[c_142,c_67])).

tff(c_530,plain,(
    ! [A_129,C_130] :
      ( r2_hidden('#skF_5'(A_129,'#skF_7',C_130),C_130)
      | k10_relat_1(A_129,'#skF_7') = C_130
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_450,c_152])).

tff(c_564,plain,(
    ! [A_131] :
      ( k10_relat_1(A_131,'#skF_7') = '#skF_7'
      | ~ v1_relat_1(A_131) ) ),
    inference(resolution,[status(thm)],[c_530,c_152])).

tff(c_571,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_564])).

tff(c_32,plain,(
    ! [A_57] : k10_relat_1(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_596,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_32])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:30:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.41  
% 2.39/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.41  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.39/1.41  
% 2.39/1.41  %Foreground sorts:
% 2.39/1.41  
% 2.39/1.41  
% 2.39/1.41  %Background operators:
% 2.39/1.41  
% 2.39/1.41  
% 2.39/1.41  %Foreground operators:
% 2.39/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.39/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.39/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.39/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.39/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.39/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.39/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.41  
% 2.39/1.42  tff(f_91, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.39/1.42  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.39/1.42  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.39/1.42  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.39/1.42  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.39/1.42  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.39/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.39/1.42  tff(f_75, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.39/1.42  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.39/1.42  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.39/1.42  tff(c_36, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.39/1.42  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_36])).
% 2.39/1.42  tff(c_450, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_4'(A_123, B_124, C_125), B_124) | r2_hidden('#skF_5'(A_123, B_124, C_125), C_125) | k10_relat_1(A_123, B_124)=C_125 | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.42  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.42  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.42  tff(c_84, plain, (![D_79, A_80, B_81]: (~r2_hidden(D_79, '#skF_2'(A_80, B_81)) | ~r2_hidden(D_79, B_81) | ~r2_hidden(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.42  tff(c_110, plain, (![A_86, A_87, B_88]: (~r2_hidden('#skF_1'(A_86, '#skF_2'(A_87, B_88)), B_88) | ~r2_hidden(A_87, B_88) | r1_xboole_0(A_86, '#skF_2'(A_87, B_88)))), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.39/1.42  tff(c_135, plain, (![A_92, A_93]: (~r2_hidden(A_92, A_93) | r1_xboole_0(A_93, '#skF_2'(A_92, A_93)))), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.39/1.42  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.42  tff(c_142, plain, (![A_94, A_95]: (r1_xboole_0('#skF_2'(A_94, A_95), A_95) | ~r2_hidden(A_94, A_95))), inference(resolution, [status(thm)], [c_135, c_2])).
% 2.39/1.42  tff(c_62, plain, (![A_67, B_68]: (r2_hidden('#skF_2'(A_67, B_68), B_68) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.42  tff(c_40, plain, (![B_60]: (~r1_xboole_0(B_60, '#skF_7') | ~r2_hidden(B_60, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.39/1.42  tff(c_67, plain, (![A_67]: (~r1_xboole_0('#skF_2'(A_67, '#skF_7'), '#skF_7') | ~r2_hidden(A_67, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_40])).
% 2.39/1.42  tff(c_152, plain, (![A_94]: (~r2_hidden(A_94, '#skF_7'))), inference(resolution, [status(thm)], [c_142, c_67])).
% 2.39/1.42  tff(c_530, plain, (![A_129, C_130]: (r2_hidden('#skF_5'(A_129, '#skF_7', C_130), C_130) | k10_relat_1(A_129, '#skF_7')=C_130 | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_450, c_152])).
% 2.39/1.42  tff(c_564, plain, (![A_131]: (k10_relat_1(A_131, '#skF_7')='#skF_7' | ~v1_relat_1(A_131))), inference(resolution, [status(thm)], [c_530, c_152])).
% 2.39/1.42  tff(c_571, plain, (k10_relat_1(k1_xboole_0, '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_564])).
% 2.39/1.42  tff(c_32, plain, (![A_57]: (k10_relat_1(k1_xboole_0, A_57)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.39/1.42  tff(c_596, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_571, c_32])).
% 2.39/1.42  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_596])).
% 2.39/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.42  
% 2.39/1.42  Inference rules
% 2.39/1.42  ----------------------
% 2.39/1.42  #Ref     : 0
% 2.39/1.42  #Sup     : 120
% 2.39/1.42  #Fact    : 0
% 2.39/1.42  #Define  : 0
% 2.39/1.42  #Split   : 1
% 2.39/1.42  #Chain   : 0
% 2.39/1.42  #Close   : 0
% 2.39/1.42  
% 2.39/1.42  Ordering : KBO
% 2.39/1.42  
% 2.39/1.42  Simplification rules
% 2.39/1.42  ----------------------
% 2.39/1.42  #Subsume      : 40
% 2.39/1.42  #Demod        : 41
% 2.39/1.42  #Tautology    : 18
% 2.39/1.42  #SimpNegUnit  : 3
% 2.39/1.42  #BackRed      : 1
% 2.39/1.42  
% 2.39/1.42  #Partial instantiations: 0
% 2.39/1.42  #Strategies tried      : 1
% 2.39/1.42  
% 2.39/1.42  Timing (in seconds)
% 2.39/1.42  ----------------------
% 2.39/1.42  Preprocessing        : 0.31
% 2.39/1.42  Parsing              : 0.17
% 2.39/1.42  CNF conversion       : 0.03
% 2.39/1.42  Main loop            : 0.27
% 2.39/1.42  Inferencing          : 0.11
% 2.39/1.42  Reduction            : 0.07
% 2.39/1.43  Demodulation         : 0.05
% 2.39/1.43  BG Simplification    : 0.02
% 2.39/1.43  Subsumption          : 0.06
% 2.39/1.43  Abstraction          : 0.01
% 2.39/1.43  MUC search           : 0.00
% 2.39/1.43  Cooper               : 0.00
% 2.39/1.43  Total                : 0.61
% 2.39/1.43  Index Insertion      : 0.00
% 2.39/1.43  Index Deletion       : 0.00
% 2.39/1.43  Index Matching       : 0.00
% 2.39/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
