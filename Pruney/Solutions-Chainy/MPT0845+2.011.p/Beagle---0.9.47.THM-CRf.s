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
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 183 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_75,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    ! [A_58] : v1_relat_1(k6_relat_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_420,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden('#skF_4'(A_139,B_140,C_141),B_140)
      | r2_hidden('#skF_5'(A_139,B_140,C_141),C_141)
      | k10_relat_1(A_139,B_140) = C_141
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    ! [D_92,A_93,B_94] :
      ( ~ r2_hidden(D_92,'#skF_2'(A_93,B_94))
      | ~ r2_hidden(D_92,B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_99,B_100,B_101] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_99,B_100),B_101),B_100)
      | ~ r2_hidden(A_99,B_100)
      | r1_xboole_0('#skF_2'(A_99,B_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_167,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden(A_102,B_103)
      | r1_xboole_0('#skF_2'(A_102,B_103),B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_161])).

tff(c_59,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [B_62] :
      ( ~ r1_xboole_0(B_62,'#skF_7')
      | ~ r2_hidden(B_62,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ! [A_73] :
      ( ~ r1_xboole_0('#skF_2'(A_73,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_59,c_40])).

tff(c_177,plain,(
    ! [A_102] : ~ r2_hidden(A_102,'#skF_7') ),
    inference(resolution,[status(thm)],[c_167,c_68])).

tff(c_513,plain,(
    ! [A_148,C_149] :
      ( r2_hidden('#skF_5'(A_148,'#skF_7',C_149),C_149)
      | k10_relat_1(A_148,'#skF_7') = C_149
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_420,c_177])).

tff(c_556,plain,(
    ! [A_150] :
      ( k10_relat_1(A_150,'#skF_7') = '#skF_7'
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_513,c_177])).

tff(c_560,plain,(
    ! [A_58] : k10_relat_1(k6_relat_1(A_58),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_556])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_80,plain,(
    ! [B_78,A_79] :
      ( ~ r1_tarski(B_78,'#skF_2'(A_79,B_78))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_59,c_38])).

tff(c_85,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_604,plain,(
    ! [A_152] :
      ( k10_relat_1(A_152,'#skF_7') = k1_xboole_0
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_513,c_85])).

tff(c_607,plain,(
    ! [A_58] : k10_relat_1(k6_relat_1(A_58),'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_604])).

tff(c_609,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_607])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.36  
% 2.38/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.38/1.36  
% 2.38/1.36  %Foreground sorts:
% 2.38/1.36  
% 2.38/1.36  
% 2.38/1.36  %Background operators:
% 2.38/1.36  
% 2.38/1.36  
% 2.38/1.36  %Foreground operators:
% 2.38/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.38/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.38/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.38/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.38/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.36  
% 2.38/1.37  tff(f_95, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.38/1.37  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.38/1.37  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.38/1.37  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.37  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.38/1.37  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.37  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.38/1.37  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.37  tff(c_34, plain, (![A_58]: (v1_relat_1(k6_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.38/1.37  tff(c_420, plain, (![A_139, B_140, C_141]: (r2_hidden('#skF_4'(A_139, B_140, C_141), B_140) | r2_hidden('#skF_5'(A_139, B_140, C_141), C_141) | k10_relat_1(A_139, B_140)=C_141 | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.38/1.37  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.38/1.37  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.38/1.37  tff(c_135, plain, (![D_92, A_93, B_94]: (~r2_hidden(D_92, '#skF_2'(A_93, B_94)) | ~r2_hidden(D_92, B_94) | ~r2_hidden(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.37  tff(c_161, plain, (![A_99, B_100, B_101]: (~r2_hidden('#skF_1'('#skF_2'(A_99, B_100), B_101), B_100) | ~r2_hidden(A_99, B_100) | r1_xboole_0('#skF_2'(A_99, B_100), B_101))), inference(resolution, [status(thm)], [c_8, c_135])).
% 2.38/1.37  tff(c_167, plain, (![A_102, B_103]: (~r2_hidden(A_102, B_103) | r1_xboole_0('#skF_2'(A_102, B_103), B_103))), inference(resolution, [status(thm)], [c_6, c_161])).
% 2.38/1.37  tff(c_59, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.38/1.37  tff(c_40, plain, (![B_62]: (~r1_xboole_0(B_62, '#skF_7') | ~r2_hidden(B_62, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.37  tff(c_68, plain, (![A_73]: (~r1_xboole_0('#skF_2'(A_73, '#skF_7'), '#skF_7') | ~r2_hidden(A_73, '#skF_7'))), inference(resolution, [status(thm)], [c_59, c_40])).
% 2.38/1.37  tff(c_177, plain, (![A_102]: (~r2_hidden(A_102, '#skF_7'))), inference(resolution, [status(thm)], [c_167, c_68])).
% 2.38/1.37  tff(c_513, plain, (![A_148, C_149]: (r2_hidden('#skF_5'(A_148, '#skF_7', C_149), C_149) | k10_relat_1(A_148, '#skF_7')=C_149 | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_420, c_177])).
% 2.38/1.37  tff(c_556, plain, (![A_150]: (k10_relat_1(A_150, '#skF_7')='#skF_7' | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_513, c_177])).
% 2.38/1.37  tff(c_560, plain, (![A_58]: (k10_relat_1(k6_relat_1(A_58), '#skF_7')='#skF_7')), inference(resolution, [status(thm)], [c_34, c_556])).
% 2.38/1.37  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.37  tff(c_38, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.37  tff(c_80, plain, (![B_78, A_79]: (~r1_tarski(B_78, '#skF_2'(A_79, B_78)) | ~r2_hidden(A_79, B_78))), inference(resolution, [status(thm)], [c_59, c_38])).
% 2.38/1.37  tff(c_85, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_80])).
% 2.38/1.37  tff(c_604, plain, (![A_152]: (k10_relat_1(A_152, '#skF_7')=k1_xboole_0 | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_513, c_85])).
% 2.38/1.37  tff(c_607, plain, (![A_58]: (k10_relat_1(k6_relat_1(A_58), '#skF_7')=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_604])).
% 2.38/1.37  tff(c_609, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_607])).
% 2.38/1.37  tff(c_611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_609])).
% 2.38/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.37  
% 2.38/1.37  Inference rules
% 2.38/1.37  ----------------------
% 2.38/1.37  #Ref     : 0
% 2.38/1.37  #Sup     : 118
% 2.38/1.38  #Fact    : 0
% 2.38/1.38  #Define  : 0
% 2.38/1.38  #Split   : 0
% 2.38/1.38  #Chain   : 0
% 2.38/1.38  #Close   : 0
% 2.38/1.38  
% 2.38/1.38  Ordering : KBO
% 2.38/1.38  
% 2.38/1.38  Simplification rules
% 2.38/1.38  ----------------------
% 2.38/1.38  #Subsume      : 42
% 2.38/1.38  #Demod        : 21
% 2.38/1.38  #Tautology    : 12
% 2.38/1.38  #SimpNegUnit  : 2
% 2.38/1.38  #BackRed      : 0
% 2.38/1.38  
% 2.38/1.38  #Partial instantiations: 0
% 2.38/1.38  #Strategies tried      : 1
% 2.38/1.38  
% 2.38/1.38  Timing (in seconds)
% 2.38/1.38  ----------------------
% 2.38/1.38  Preprocessing        : 0.32
% 2.38/1.38  Parsing              : 0.16
% 2.38/1.38  CNF conversion       : 0.03
% 2.38/1.38  Main loop            : 0.28
% 2.38/1.38  Inferencing          : 0.11
% 2.38/1.38  Reduction            : 0.07
% 2.38/1.38  Demodulation         : 0.05
% 2.38/1.38  BG Simplification    : 0.02
% 2.38/1.38  Subsumption          : 0.06
% 2.38/1.38  Abstraction          : 0.01
% 2.38/1.38  MUC search           : 0.00
% 2.38/1.38  Cooper               : 0.00
% 2.38/1.38  Total                : 0.63
% 2.38/1.38  Index Insertion      : 0.00
% 2.38/1.38  Index Deletion       : 0.00
% 2.38/1.38  Index Matching       : 0.00
% 2.38/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
