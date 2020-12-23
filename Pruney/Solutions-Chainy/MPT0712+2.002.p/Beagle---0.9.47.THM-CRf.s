%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 126 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
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

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_130,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,B_56)
      | ~ r2_hidden(C_57,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_134,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_130])).

tff(c_148,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,k1_relat_1(B_26))
      | k11_relat_1(B_26,A_25) = k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_252,plain,(
    ! [C_72,A_73,B_74] :
      ( k2_tarski(k1_funct_1(C_72,A_73),k1_funct_1(C_72,B_74)) = k9_relat_1(C_72,k2_tarski(A_73,B_74))
      | ~ r2_hidden(B_74,k1_relat_1(C_72))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_259,plain,(
    ! [C_72,B_74] :
      ( k9_relat_1(C_72,k2_tarski(B_74,B_74)) = k1_tarski(k1_funct_1(C_72,B_74))
      | ~ r2_hidden(B_74,k1_relat_1(C_72))
      | ~ r2_hidden(B_74,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_24])).

tff(c_512,plain,(
    ! [C_135,B_136] :
      ( k9_relat_1(C_135,k1_tarski(B_136)) = k1_tarski(k1_funct_1(C_135,B_136))
      | ~ r2_hidden(B_136,k1_relat_1(C_135))
      | ~ r2_hidden(B_136,k1_relat_1(C_135))
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_259])).

tff(c_550,plain,(
    ! [B_158,A_159] :
      ( k9_relat_1(B_158,k1_tarski(A_159)) = k1_tarski(k1_funct_1(B_158,A_159))
      | ~ r2_hidden(A_159,k1_relat_1(B_158))
      | ~ v1_funct_1(B_158)
      | k11_relat_1(B_158,A_159) = k1_xboole_0
      | ~ v1_relat_1(B_158) ) ),
    inference(resolution,[status(thm)],[c_34,c_512])).

tff(c_613,plain,(
    ! [B_162,A_163] :
      ( k9_relat_1(B_162,k1_tarski(A_163)) = k1_tarski(k1_funct_1(B_162,A_163))
      | ~ v1_funct_1(B_162)
      | k11_relat_1(B_162,A_163) = k1_xboole_0
      | ~ v1_relat_1(B_162) ) ),
    inference(resolution,[status(thm)],[c_34,c_550])).

tff(c_88,plain,(
    ! [B_45,A_46] :
      ( k2_relat_1(k7_relat_1(B_45,A_46)) = k9_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_94,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4',k1_tarski('#skF_3')),k1_tarski(k1_funct_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_40])).

tff(c_100,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k1_tarski('#skF_3')),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_94])).

tff(c_619,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_4','#skF_3')),k1_tarski(k1_funct_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_100])).

tff(c_631,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_18,c_619])).

tff(c_30,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(A_20,k1_tarski(B_22)) = k11_relat_1(A_20,B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_152,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_154,plain,(
    ~ r1_tarski(k11_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_633,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_154])).

tff(c_636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.39  
% 2.62/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.62/1.39  
% 2.62/1.39  %Foreground sorts:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Background operators:
% 2.62/1.39  
% 2.62/1.39  
% 2.62/1.39  %Foreground operators:
% 2.62/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.62/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.62/1.39  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.62/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.62/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.62/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.62/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.39  
% 2.90/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.90/1.41  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.90/1.41  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.90/1.41  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 2.90/1.41  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.41  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.90/1.41  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.41  tff(f_100, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 2.90/1.41  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.90/1.41  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.90/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.90/1.41  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.90/1.41  tff(c_130, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, B_56) | ~r2_hidden(C_57, A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.90/1.41  tff(c_134, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_130])).
% 2.90/1.41  tff(c_148, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_134])).
% 2.90/1.41  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.41  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.41  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.90/1.41  tff(c_34, plain, (![A_25, B_26]: (r2_hidden(A_25, k1_relat_1(B_26)) | k11_relat_1(B_26, A_25)=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.90/1.41  tff(c_24, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.41  tff(c_252, plain, (![C_72, A_73, B_74]: (k2_tarski(k1_funct_1(C_72, A_73), k1_funct_1(C_72, B_74))=k9_relat_1(C_72, k2_tarski(A_73, B_74)) | ~r2_hidden(B_74, k1_relat_1(C_72)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.90/1.41  tff(c_259, plain, (![C_72, B_74]: (k9_relat_1(C_72, k2_tarski(B_74, B_74))=k1_tarski(k1_funct_1(C_72, B_74)) | ~r2_hidden(B_74, k1_relat_1(C_72)) | ~r2_hidden(B_74, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_252, c_24])).
% 2.90/1.41  tff(c_512, plain, (![C_135, B_136]: (k9_relat_1(C_135, k1_tarski(B_136))=k1_tarski(k1_funct_1(C_135, B_136)) | ~r2_hidden(B_136, k1_relat_1(C_135)) | ~r2_hidden(B_136, k1_relat_1(C_135)) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_259])).
% 2.90/1.41  tff(c_550, plain, (![B_158, A_159]: (k9_relat_1(B_158, k1_tarski(A_159))=k1_tarski(k1_funct_1(B_158, A_159)) | ~r2_hidden(A_159, k1_relat_1(B_158)) | ~v1_funct_1(B_158) | k11_relat_1(B_158, A_159)=k1_xboole_0 | ~v1_relat_1(B_158))), inference(resolution, [status(thm)], [c_34, c_512])).
% 2.90/1.41  tff(c_613, plain, (![B_162, A_163]: (k9_relat_1(B_162, k1_tarski(A_163))=k1_tarski(k1_funct_1(B_162, A_163)) | ~v1_funct_1(B_162) | k11_relat_1(B_162, A_163)=k1_xboole_0 | ~v1_relat_1(B_162))), inference(resolution, [status(thm)], [c_34, c_550])).
% 2.90/1.41  tff(c_88, plain, (![B_45, A_46]: (k2_relat_1(k7_relat_1(B_45, A_46))=k9_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.90/1.41  tff(c_40, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3'))), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.41  tff(c_94, plain, (~r1_tarski(k9_relat_1('#skF_4', k1_tarski('#skF_3')), k1_tarski(k1_funct_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_88, c_40])).
% 2.90/1.41  tff(c_100, plain, (~r1_tarski(k9_relat_1('#skF_4', k1_tarski('#skF_3')), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_94])).
% 2.90/1.41  tff(c_619, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_4', '#skF_3')), k1_tarski(k1_funct_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_613, c_100])).
% 2.90/1.41  tff(c_631, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_18, c_619])).
% 2.90/1.41  tff(c_30, plain, (![A_20, B_22]: (k9_relat_1(A_20, k1_tarski(B_22))=k11_relat_1(A_20, B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.90/1.41  tff(c_152, plain, (~r1_tarski(k11_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_100])).
% 2.90/1.41  tff(c_154, plain, (~r1_tarski(k11_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_152])).
% 2.90/1.41  tff(c_633, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_154])).
% 2.90/1.41  tff(c_636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_633])).
% 2.90/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.41  
% 2.90/1.41  Inference rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Ref     : 0
% 2.90/1.41  #Sup     : 132
% 2.90/1.41  #Fact    : 0
% 2.90/1.41  #Define  : 0
% 2.90/1.41  #Split   : 0
% 2.90/1.41  #Chain   : 0
% 2.90/1.41  #Close   : 0
% 2.90/1.41  
% 2.90/1.41  Ordering : KBO
% 2.90/1.41  
% 2.90/1.41  Simplification rules
% 2.90/1.41  ----------------------
% 2.90/1.41  #Subsume      : 45
% 2.90/1.41  #Demod        : 17
% 2.90/1.41  #Tautology    : 31
% 2.90/1.41  #SimpNegUnit  : 0
% 2.90/1.41  #BackRed      : 1
% 2.90/1.41  
% 2.90/1.41  #Partial instantiations: 0
% 2.90/1.41  #Strategies tried      : 1
% 2.90/1.41  
% 2.90/1.41  Timing (in seconds)
% 2.90/1.41  ----------------------
% 2.90/1.41  Preprocessing        : 0.32
% 2.90/1.41  Parsing              : 0.17
% 2.90/1.41  CNF conversion       : 0.02
% 2.90/1.41  Main loop            : 0.32
% 2.90/1.41  Inferencing          : 0.12
% 2.90/1.41  Reduction            : 0.08
% 2.90/1.41  Demodulation         : 0.06
% 2.90/1.41  BG Simplification    : 0.02
% 2.90/1.41  Subsumption          : 0.08
% 2.90/1.41  Abstraction          : 0.02
% 2.90/1.41  MUC search           : 0.00
% 2.90/1.41  Cooper               : 0.00
% 2.90/1.41  Total                : 0.66
% 2.90/1.41  Index Insertion      : 0.00
% 2.90/1.41  Index Deletion       : 0.00
% 2.90/1.41  Index Matching       : 0.00
% 2.90/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
