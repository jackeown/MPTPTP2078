%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   70 (  87 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 137 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_86,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [A_52,B_53] : r2_hidden(A_52,k2_tarski(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_6])).

tff(c_148,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_145])).

tff(c_76,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_72,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    ! [A_28] : k2_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_158,plain,(
    ! [A_67] :
      ( k10_relat_1(A_67,k2_relat_1(A_67)) = k1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_167,plain,(
    ! [A_28] :
      ( k10_relat_1(k6_relat_1(A_28),A_28) = k1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_158])).

tff(c_171,plain,(
    ! [A_28] : k10_relat_1(k6_relat_1(A_28),A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_167])).

tff(c_193,plain,(
    ! [B_87,A_88] :
      ( k10_relat_1(B_87,k1_tarski(A_88)) != k1_xboole_0
      | ~ r2_hidden(A_88,k2_relat_1(B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_196,plain,(
    ! [A_28,A_88] :
      ( k10_relat_1(k6_relat_1(A_28),k1_tarski(A_88)) != k1_xboole_0
      | ~ r2_hidden(A_88,A_28)
      | ~ v1_relat_1(k6_relat_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_193])).

tff(c_199,plain,(
    ! [A_89,A_90] :
      ( k10_relat_1(k6_relat_1(A_89),k1_tarski(A_90)) != k1_xboole_0
      | ~ r2_hidden(A_90,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_196])).

tff(c_203,plain,(
    ! [A_90] :
      ( k1_tarski(A_90) != k1_xboole_0
      | ~ r2_hidden(A_90,k1_tarski(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_199])).

tff(c_205,plain,(
    ! [A_90] : k1_tarski(A_90) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_203])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_92,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_88,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_428,plain,(
    ! [D_152,C_153,B_154,A_155] :
      ( r2_hidden(k1_funct_1(D_152,C_153),B_154)
      | k1_xboole_0 = B_154
      | ~ r2_hidden(C_153,A_155)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2(D_152,A_155,B_154)
      | ~ v1_funct_1(D_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_483,plain,(
    ! [D_156,B_157] :
      ( r2_hidden(k1_funct_1(D_156,'#skF_7'),B_157)
      | k1_xboole_0 = B_157
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_157)))
      | ~ v1_funct_2(D_156,'#skF_5',B_157)
      | ~ v1_funct_1(D_156) ) ),
    inference(resolution,[status(thm)],[c_88,c_428])).

tff(c_486,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_483])).

tff(c_489,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_486])).

tff(c_490,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_489])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_287,plain,(
    ! [E_116,C_117,B_118,A_119] :
      ( E_116 = C_117
      | E_116 = B_118
      | E_116 = A_119
      | ~ r2_hidden(E_116,k1_enumset1(A_119,B_118,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_306,plain,(
    ! [E_120,B_121,A_122] :
      ( E_120 = B_121
      | E_120 = A_122
      | E_120 = A_122
      | ~ r2_hidden(E_120,k2_tarski(A_122,B_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_287])).

tff(c_315,plain,(
    ! [E_120,A_8] :
      ( E_120 = A_8
      | E_120 = A_8
      | E_120 = A_8
      | ~ r2_hidden(E_120,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_306])).

tff(c_495,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_490,c_315])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_86,c_86,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.45  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.45  
% 2.87/1.45  %Foreground sorts:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Background operators:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Foreground operators:
% 2.87/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.87/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.87/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.87/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.45  
% 2.87/1.46  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.87/1.46  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.87/1.46  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.46  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.87/1.46  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.87/1.46  tff(f_77, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.87/1.46  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.87/1.46  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.87/1.46  tff(f_100, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.87/1.46  tff(c_86, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.87/1.46  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.46  tff(c_127, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.46  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.46  tff(c_145, plain, (![A_52, B_53]: (r2_hidden(A_52, k2_tarski(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_6])).
% 2.87/1.46  tff(c_148, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_145])).
% 2.87/1.46  tff(c_76, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.87/1.46  tff(c_72, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.46  tff(c_74, plain, (![A_28]: (k2_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.87/1.46  tff(c_158, plain, (![A_67]: (k10_relat_1(A_67, k2_relat_1(A_67))=k1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.87/1.46  tff(c_167, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=k1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_158])).
% 2.87/1.46  tff(c_171, plain, (![A_28]: (k10_relat_1(k6_relat_1(A_28), A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_167])).
% 2.87/1.46  tff(c_193, plain, (![B_87, A_88]: (k10_relat_1(B_87, k1_tarski(A_88))!=k1_xboole_0 | ~r2_hidden(A_88, k2_relat_1(B_87)) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.87/1.46  tff(c_196, plain, (![A_28, A_88]: (k10_relat_1(k6_relat_1(A_28), k1_tarski(A_88))!=k1_xboole_0 | ~r2_hidden(A_88, A_28) | ~v1_relat_1(k6_relat_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_193])).
% 2.87/1.46  tff(c_199, plain, (![A_89, A_90]: (k10_relat_1(k6_relat_1(A_89), k1_tarski(A_90))!=k1_xboole_0 | ~r2_hidden(A_90, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_196])).
% 2.87/1.46  tff(c_203, plain, (![A_90]: (k1_tarski(A_90)!=k1_xboole_0 | ~r2_hidden(A_90, k1_tarski(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_199])).
% 2.87/1.46  tff(c_205, plain, (![A_90]: (k1_tarski(A_90)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_203])).
% 2.87/1.46  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.87/1.46  tff(c_92, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.87/1.46  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.87/1.46  tff(c_88, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.87/1.46  tff(c_428, plain, (![D_152, C_153, B_154, A_155]: (r2_hidden(k1_funct_1(D_152, C_153), B_154) | k1_xboole_0=B_154 | ~r2_hidden(C_153, A_155) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2(D_152, A_155, B_154) | ~v1_funct_1(D_152))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.46  tff(c_483, plain, (![D_156, B_157]: (r2_hidden(k1_funct_1(D_156, '#skF_7'), B_157) | k1_xboole_0=B_157 | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_157))) | ~v1_funct_2(D_156, '#skF_5', B_157) | ~v1_funct_1(D_156))), inference(resolution, [status(thm)], [c_88, c_428])).
% 2.87/1.46  tff(c_486, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_90, c_483])).
% 2.87/1.46  tff(c_489, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_486])).
% 2.87/1.46  tff(c_490, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_205, c_489])).
% 2.87/1.46  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.87/1.46  tff(c_287, plain, (![E_116, C_117, B_118, A_119]: (E_116=C_117 | E_116=B_118 | E_116=A_119 | ~r2_hidden(E_116, k1_enumset1(A_119, B_118, C_117)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.46  tff(c_306, plain, (![E_120, B_121, A_122]: (E_120=B_121 | E_120=A_122 | E_120=A_122 | ~r2_hidden(E_120, k2_tarski(A_122, B_121)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_287])).
% 2.87/1.46  tff(c_315, plain, (![E_120, A_8]: (E_120=A_8 | E_120=A_8 | E_120=A_8 | ~r2_hidden(E_120, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_306])).
% 2.87/1.46  tff(c_495, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_490, c_315])).
% 2.87/1.46  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_86, c_86, c_495])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 89
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 0
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 1
% 2.87/1.46  #Demod        : 16
% 2.87/1.46  #Tautology    : 44
% 2.87/1.46  #SimpNegUnit  : 4
% 2.87/1.46  #BackRed      : 0
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.37
% 2.87/1.46  Parsing              : 0.19
% 2.87/1.46  CNF conversion       : 0.03
% 2.87/1.46  Main loop            : 0.31
% 2.87/1.46  Inferencing          : 0.10
% 2.87/1.47  Reduction            : 0.09
% 2.87/1.47  Demodulation         : 0.07
% 2.87/1.47  BG Simplification    : 0.02
% 2.87/1.47  Subsumption          : 0.07
% 2.87/1.47  Abstraction          : 0.03
% 2.87/1.47  MUC search           : 0.00
% 2.87/1.47  Cooper               : 0.00
% 2.87/1.47  Total                : 0.71
% 2.87/1.47  Index Insertion      : 0.00
% 2.87/1.47  Index Deletion       : 0.00
% 2.87/1.47  Index Matching       : 0.00
% 2.87/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
