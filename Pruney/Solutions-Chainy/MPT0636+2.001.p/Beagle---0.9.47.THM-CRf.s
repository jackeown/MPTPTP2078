%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 274 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(c_54,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))))
    | r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_80,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_58,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6'))))
    | r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_79,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_28,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_14] : v1_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_14])).

tff(c_82,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,k1_relat_1(C_35))
      | ~ r2_hidden(k4_tarski(A_34,B_36),C_35)
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_89,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(D_8,k1_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(resolution,[status(thm)],[c_64,c_82])).

tff(c_93,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(D_8,k1_relat_1(k6_relat_1(A_1)))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_89])).

tff(c_1821,plain,(
    ! [A_135,C_136,B_137] :
      ( r2_hidden(A_135,k1_relat_1(k5_relat_1(C_136,B_137)))
      | ~ r2_hidden(k1_funct_1(C_136,A_135),k1_relat_1(B_137))
      | ~ r2_hidden(A_135,k1_relat_1(C_136))
      | ~ v1_funct_1(C_136)
      | ~ v1_relat_1(C_136)
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1860,plain,(
    ! [A_135,C_136,A_1] :
      ( r2_hidden(A_135,k1_relat_1(k5_relat_1(C_136,k6_relat_1(A_1))))
      | ~ r2_hidden(A_135,k1_relat_1(C_136))
      | ~ v1_funct_1(C_136)
      | ~ v1_relat_1(C_136)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ r2_hidden(k1_funct_1(C_136,A_135),A_1) ) ),
    inference(resolution,[status(thm)],[c_93,c_1821])).

tff(c_1884,plain,(
    ! [A_138,C_139,A_140] :
      ( r2_hidden(A_138,k1_relat_1(k5_relat_1(C_139,k6_relat_1(A_140))))
      | ~ r2_hidden(A_138,k1_relat_1(C_139))
      | ~ v1_funct_1(C_139)
      | ~ v1_relat_1(C_139)
      | ~ r2_hidden(k1_funct_1(C_139,A_138),A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1860])).

tff(c_48,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_193,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80,c_48])).

tff(c_1935,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1884,c_193])).

tff(c_1974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_46,c_44,c_79,c_1935])).

tff(c_1976,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1975,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2505,plain,(
    ! [C_187,A_188,B_189] :
      ( r2_hidden(k1_funct_1(C_187,A_188),k1_relat_1(B_189))
      | ~ r2_hidden(A_188,k1_relat_1(k5_relat_1(C_187,B_189)))
      | ~ v1_funct_1(C_187)
      | ~ v1_relat_1(C_187)
      | ~ v1_funct_1(B_189)
      | ~ v1_relat_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2022,plain,(
    ! [A_153,C_154] :
      ( r2_hidden(k4_tarski(A_153,k1_funct_1(C_154,A_153)),C_154)
      | ~ r2_hidden(A_153,k1_relat_1(C_154))
      | ~ v1_funct_1(C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18])).

tff(c_2032,plain,(
    ! [A_153,A_1] :
      ( r2_hidden(A_153,A_1)
      | ~ r2_hidden(A_153,k1_relat_1(k6_relat_1(A_1)))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2022,c_60])).

tff(c_2045,plain,(
    ! [A_153,A_1] :
      ( r2_hidden(A_153,A_1)
      | ~ r2_hidden(A_153,k1_relat_1(k6_relat_1(A_1))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2032])).

tff(c_2517,plain,(
    ! [C_187,A_188,A_1] :
      ( r2_hidden(k1_funct_1(C_187,A_188),A_1)
      | ~ r2_hidden(A_188,k1_relat_1(k5_relat_1(C_187,k6_relat_1(A_1))))
      | ~ v1_funct_1(C_187)
      | ~ v1_relat_1(C_187)
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_2505,c_2045])).

tff(c_2555,plain,(
    ! [C_190,A_191,A_192] :
      ( r2_hidden(k1_funct_1(C_190,A_191),A_192)
      | ~ r2_hidden(A_191,k1_relat_1(k5_relat_1(C_190,k6_relat_1(A_192))))
      | ~ v1_funct_1(C_190)
      | ~ v1_relat_1(C_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2517])).

tff(c_2594,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_1975,c_2555])).

tff(c_2606,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2594])).

tff(c_2608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1976,c_2606])).

tff(c_2610,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2609,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_7',k6_relat_1('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2947,plain,(
    ! [A_221,C_222,B_223] :
      ( r2_hidden(A_221,k1_relat_1(C_222))
      | ~ r2_hidden(A_221,k1_relat_1(k5_relat_1(C_222,B_223)))
      | ~ v1_funct_1(C_222)
      | ~ v1_relat_1(C_222)
      | ~ v1_funct_1(B_223)
      | ~ v1_relat_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2958,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k6_relat_1('#skF_6'))
    | ~ v1_relat_1(k6_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2609,c_2947])).

tff(c_2963,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_46,c_44,c_2958])).

tff(c_2965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2610,c_2963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.90  
% 4.68/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.91  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.68/1.91  
% 4.68/1.91  %Foreground sorts:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Background operators:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Foreground operators:
% 4.68/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.68/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.68/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.68/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.91  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.68/1.91  
% 4.68/1.92  tff(f_94, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 4.68/1.92  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.68/1.92  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 4.68/1.92  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.68/1.92  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 4.68/1.92  tff(c_54, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6')))) | r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.92  tff(c_80, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_54])).
% 4.68/1.92  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.92  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.92  tff(c_58, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6')))) | r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.92  tff(c_79, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.68/1.92  tff(c_28, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.92  tff(c_30, plain, (![A_14]: (v1_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.92  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.92  tff(c_64, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_14])).
% 4.68/1.92  tff(c_82, plain, (![A_34, C_35, B_36]: (r2_hidden(A_34, k1_relat_1(C_35)) | ~r2_hidden(k4_tarski(A_34, B_36), C_35) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.68/1.92  tff(c_89, plain, (![D_8, A_1]: (r2_hidden(D_8, k1_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(resolution, [status(thm)], [c_64, c_82])).
% 4.68/1.92  tff(c_93, plain, (![D_8, A_1]: (r2_hidden(D_8, k1_relat_1(k6_relat_1(A_1))) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_89])).
% 4.68/1.92  tff(c_1821, plain, (![A_135, C_136, B_137]: (r2_hidden(A_135, k1_relat_1(k5_relat_1(C_136, B_137))) | ~r2_hidden(k1_funct_1(C_136, A_135), k1_relat_1(B_137)) | ~r2_hidden(A_135, k1_relat_1(C_136)) | ~v1_funct_1(C_136) | ~v1_relat_1(C_136) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.92  tff(c_1860, plain, (![A_135, C_136, A_1]: (r2_hidden(A_135, k1_relat_1(k5_relat_1(C_136, k6_relat_1(A_1)))) | ~r2_hidden(A_135, k1_relat_1(C_136)) | ~v1_funct_1(C_136) | ~v1_relat_1(C_136) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~r2_hidden(k1_funct_1(C_136, A_135), A_1))), inference(resolution, [status(thm)], [c_93, c_1821])).
% 4.68/1.92  tff(c_1884, plain, (![A_138, C_139, A_140]: (r2_hidden(A_138, k1_relat_1(k5_relat_1(C_139, k6_relat_1(A_140)))) | ~r2_hidden(A_138, k1_relat_1(C_139)) | ~v1_funct_1(C_139) | ~v1_relat_1(C_139) | ~r2_hidden(k1_funct_1(C_139, A_138), A_140))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1860])).
% 4.68/1.92  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.68/1.92  tff(c_193, plain, (~r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80, c_48])).
% 4.68/1.92  tff(c_1935, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_1884, c_193])).
% 4.68/1.92  tff(c_1974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_46, c_44, c_79, c_1935])).
% 4.68/1.92  tff(c_1976, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_54])).
% 4.68/1.92  tff(c_1975, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_54])).
% 4.68/1.92  tff(c_2505, plain, (![C_187, A_188, B_189]: (r2_hidden(k1_funct_1(C_187, A_188), k1_relat_1(B_189)) | ~r2_hidden(A_188, k1_relat_1(k5_relat_1(C_187, B_189))) | ~v1_funct_1(C_187) | ~v1_relat_1(C_187) | ~v1_funct_1(B_189) | ~v1_relat_1(B_189))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.92  tff(c_2022, plain, (![A_153, C_154]: (r2_hidden(k4_tarski(A_153, k1_funct_1(C_154, A_153)), C_154) | ~r2_hidden(A_153, k1_relat_1(C_154)) | ~v1_funct_1(C_154) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.68/1.92  tff(c_18, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.92  tff(c_60, plain, (![C_7, A_1, D_8]: (r2_hidden(C_7, A_1) | ~r2_hidden(k4_tarski(C_7, D_8), k6_relat_1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18])).
% 4.68/1.92  tff(c_2032, plain, (![A_153, A_1]: (r2_hidden(A_153, A_1) | ~r2_hidden(A_153, k1_relat_1(k6_relat_1(A_1))) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(resolution, [status(thm)], [c_2022, c_60])).
% 4.68/1.92  tff(c_2045, plain, (![A_153, A_1]: (r2_hidden(A_153, A_1) | ~r2_hidden(A_153, k1_relat_1(k6_relat_1(A_1))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2032])).
% 4.68/1.92  tff(c_2517, plain, (![C_187, A_188, A_1]: (r2_hidden(k1_funct_1(C_187, A_188), A_1) | ~r2_hidden(A_188, k1_relat_1(k5_relat_1(C_187, k6_relat_1(A_1)))) | ~v1_funct_1(C_187) | ~v1_relat_1(C_187) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(resolution, [status(thm)], [c_2505, c_2045])).
% 4.68/1.92  tff(c_2555, plain, (![C_190, A_191, A_192]: (r2_hidden(k1_funct_1(C_190, A_191), A_192) | ~r2_hidden(A_191, k1_relat_1(k5_relat_1(C_190, k6_relat_1(A_192)))) | ~v1_funct_1(C_190) | ~v1_relat_1(C_190))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2517])).
% 4.68/1.92  tff(c_2594, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_1975, c_2555])).
% 4.68/1.92  tff(c_2606, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2594])).
% 4.68/1.92  tff(c_2608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1976, c_2606])).
% 4.68/1.92  tff(c_2610, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 4.68/1.92  tff(c_2609, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_7', k6_relat_1('#skF_6'))))), inference(splitRight, [status(thm)], [c_58])).
% 4.68/1.92  tff(c_2947, plain, (![A_221, C_222, B_223]: (r2_hidden(A_221, k1_relat_1(C_222)) | ~r2_hidden(A_221, k1_relat_1(k5_relat_1(C_222, B_223))) | ~v1_funct_1(C_222) | ~v1_relat_1(C_222) | ~v1_funct_1(B_223) | ~v1_relat_1(B_223))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.68/1.92  tff(c_2958, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k6_relat_1('#skF_6')) | ~v1_relat_1(k6_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2609, c_2947])).
% 4.68/1.92  tff(c_2963, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_46, c_44, c_2958])).
% 4.68/1.92  tff(c_2965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2610, c_2963])).
% 4.68/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.92  
% 4.68/1.92  Inference rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Ref     : 0
% 4.68/1.92  #Sup     : 581
% 4.68/1.92  #Fact    : 6
% 4.68/1.92  #Define  : 0
% 4.68/1.92  #Split   : 3
% 4.68/1.92  #Chain   : 0
% 4.68/1.92  #Close   : 0
% 4.68/1.92  
% 4.68/1.92  Ordering : KBO
% 4.68/1.92  
% 4.68/1.92  Simplification rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Subsume      : 97
% 4.68/1.92  #Demod        : 276
% 4.68/1.92  #Tautology    : 141
% 4.68/1.92  #SimpNegUnit  : 2
% 4.68/1.92  #BackRed      : 0
% 4.68/1.92  
% 4.68/1.92  #Partial instantiations: 0
% 4.68/1.92  #Strategies tried      : 1
% 4.68/1.92  
% 4.68/1.92  Timing (in seconds)
% 4.68/1.92  ----------------------
% 4.68/1.92  Preprocessing        : 0.33
% 4.68/1.92  Parsing              : 0.17
% 4.68/1.92  CNF conversion       : 0.03
% 4.68/1.92  Main loop            : 0.75
% 4.68/1.92  Inferencing          : 0.26
% 4.68/1.92  Reduction            : 0.20
% 4.68/1.92  Demodulation         : 0.14
% 4.68/1.92  BG Simplification    : 0.04
% 4.68/1.92  Subsumption          : 0.18
% 4.68/1.92  Abstraction          : 0.06
% 4.68/1.92  MUC search           : 0.00
% 4.68/1.92  Cooper               : 0.00
% 4.68/1.92  Total                : 1.11
% 4.68/1.92  Index Insertion      : 0.00
% 4.68/1.92  Index Deletion       : 0.00
% 4.68/1.92  Index Matching       : 0.00
% 4.68/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
