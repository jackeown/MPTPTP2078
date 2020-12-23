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
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 125 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_43,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_60] : v1_funct_1(k6_relat_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_12,plain,(
    ! [A_13] : k9_relat_1(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_56] : v1_relat_1(k6_relat_1(A_56)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_594,plain,(
    ! [A_158,B_159,C_160] :
      ( r2_hidden('#skF_4'(A_158,B_159,C_160),B_159)
      | r2_hidden('#skF_5'(A_158,B_159,C_160),C_160)
      | k9_relat_1(A_158,B_159) = C_160
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_87,plain,(
    ! [D_75,A_76,B_77] :
      ( ~ r2_hidden(D_75,'#skF_2'(A_76,B_77))
      | ~ r2_hidden(D_75,B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_103,plain,(
    ! [A_78,B_79,B_80] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_78,B_79),B_80),B_79)
      | ~ r2_hidden(A_78,B_79)
      | r1_xboole_0('#skF_2'(A_78,B_79),B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_109,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden(A_81,B_82)
      | r1_xboole_0('#skF_2'(A_81,B_82),B_82) ) ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_65,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [B_58] :
      ( ~ r1_xboole_0(B_58,'#skF_7')
      | ~ r2_hidden(B_58,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_70,plain,(
    ! [A_63] :
      ( ~ r1_xboole_0('#skF_2'(A_63,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_63,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_65,c_44])).

tff(c_117,plain,(
    ! [A_81] : ~ r2_hidden(A_81,'#skF_7') ),
    inference(resolution,[status(thm)],[c_109,c_70])).

tff(c_677,plain,(
    ! [A_161,C_162] :
      ( r2_hidden('#skF_5'(A_161,'#skF_7',C_162),C_162)
      | k9_relat_1(A_161,'#skF_7') = C_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_594,c_117])).

tff(c_722,plain,(
    ! [A_163] :
      ( k9_relat_1(A_163,'#skF_7') = '#skF_7'
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_677,c_117])).

tff(c_725,plain,
    ( k9_relat_1(k1_xboole_0,'#skF_7') = '#skF_7'
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_722])).

tff(c_731,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_725])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.38  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.70/1.38  
% 2.70/1.38  %Foreground sorts:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Background operators:
% 2.70/1.38  
% 2.70/1.38  
% 2.70/1.38  %Foreground operators:
% 2.70/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.70/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.70/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.70/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.70/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.70/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.38  
% 2.70/1.39  tff(f_91, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.70/1.39  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.70/1.39  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.70/1.39  tff(f_58, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.70/1.39  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.70/1.39  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.70/1.39  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.70/1.39  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.39  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.39  tff(c_54, plain, (![A_60]: (v1_funct_1(k6_relat_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.39  tff(c_56, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_54])).
% 2.70/1.39  tff(c_12, plain, (![A_13]: (k9_relat_1(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.70/1.39  tff(c_40, plain, (![A_56]: (v1_relat_1(k6_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.39  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_40])).
% 2.70/1.39  tff(c_594, plain, (![A_158, B_159, C_160]: (r2_hidden('#skF_4'(A_158, B_159, C_160), B_159) | r2_hidden('#skF_5'(A_158, B_159, C_160), C_160) | k9_relat_1(A_158, B_159)=C_160 | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.70/1.39  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.39  tff(c_87, plain, (![D_75, A_76, B_77]: (~r2_hidden(D_75, '#skF_2'(A_76, B_77)) | ~r2_hidden(D_75, B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.39  tff(c_103, plain, (![A_78, B_79, B_80]: (~r2_hidden('#skF_1'('#skF_2'(A_78, B_79), B_80), B_79) | ~r2_hidden(A_78, B_79) | r1_xboole_0('#skF_2'(A_78, B_79), B_80))), inference(resolution, [status(thm)], [c_6, c_87])).
% 2.70/1.39  tff(c_109, plain, (![A_81, B_82]: (~r2_hidden(A_81, B_82) | r1_xboole_0('#skF_2'(A_81, B_82), B_82))), inference(resolution, [status(thm)], [c_4, c_103])).
% 2.70/1.39  tff(c_65, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.39  tff(c_44, plain, (![B_58]: (~r1_xboole_0(B_58, '#skF_7') | ~r2_hidden(B_58, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.70/1.39  tff(c_70, plain, (![A_63]: (~r1_xboole_0('#skF_2'(A_63, '#skF_7'), '#skF_7') | ~r2_hidden(A_63, '#skF_7'))), inference(resolution, [status(thm)], [c_65, c_44])).
% 2.70/1.39  tff(c_117, plain, (![A_81]: (~r2_hidden(A_81, '#skF_7'))), inference(resolution, [status(thm)], [c_109, c_70])).
% 2.70/1.39  tff(c_677, plain, (![A_161, C_162]: (r2_hidden('#skF_5'(A_161, '#skF_7', C_162), C_162) | k9_relat_1(A_161, '#skF_7')=C_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_594, c_117])).
% 2.70/1.39  tff(c_722, plain, (![A_163]: (k9_relat_1(A_163, '#skF_7')='#skF_7' | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_677, c_117])).
% 2.70/1.39  tff(c_725, plain, (k9_relat_1(k1_xboole_0, '#skF_7')='#skF_7' | ~v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_722])).
% 2.70/1.39  tff(c_731, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_725])).
% 2.70/1.39  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_731])).
% 2.70/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.39  
% 2.70/1.39  Inference rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Ref     : 0
% 2.70/1.39  #Sup     : 135
% 2.70/1.39  #Fact    : 0
% 2.70/1.39  #Define  : 0
% 2.70/1.39  #Split   : 0
% 2.70/1.39  #Chain   : 0
% 2.70/1.39  #Close   : 0
% 2.70/1.39  
% 2.70/1.39  Ordering : KBO
% 2.70/1.39  
% 2.70/1.39  Simplification rules
% 2.70/1.39  ----------------------
% 2.70/1.39  #Subsume      : 50
% 2.70/1.39  #Demod        : 72
% 2.70/1.39  #Tautology    : 18
% 2.70/1.39  #SimpNegUnit  : 2
% 2.70/1.39  #BackRed      : 0
% 2.70/1.39  
% 2.70/1.39  #Partial instantiations: 0
% 2.70/1.39  #Strategies tried      : 1
% 2.70/1.39  
% 2.70/1.39  Timing (in seconds)
% 2.70/1.39  ----------------------
% 2.70/1.39  Preprocessing        : 0.31
% 2.70/1.39  Parsing              : 0.16
% 2.70/1.40  CNF conversion       : 0.03
% 2.70/1.40  Main loop            : 0.32
% 2.70/1.40  Inferencing          : 0.13
% 2.70/1.40  Reduction            : 0.08
% 2.70/1.40  Demodulation         : 0.06
% 2.70/1.40  BG Simplification    : 0.02
% 2.70/1.40  Subsumption          : 0.07
% 2.70/1.40  Abstraction          : 0.02
% 2.70/1.40  MUC search           : 0.00
% 2.70/1.40  Cooper               : 0.00
% 2.70/1.40  Total                : 0.65
% 2.70/1.40  Index Insertion      : 0.00
% 2.70/1.40  Index Deletion       : 0.00
% 2.70/1.40  Index Matching       : 0.00
% 2.70/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
