%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   70 (  87 expanded)
%              Number of leaves         :   38 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 135 expanded)
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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_84,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_124,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,(
    ! [B_51,A_52] : r2_hidden(B_51,k2_tarski(A_52,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_4])).

tff(c_145,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_142])).

tff(c_70,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_74,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_76,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_156,plain,(
    ! [A_71] :
      ( k10_relat_1(A_71,k2_relat_1(A_71)) = k1_relat_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_165,plain,(
    ! [A_29] :
      ( k10_relat_1(k6_relat_1(A_29),A_29) = k1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_156])).

tff(c_169,plain,(
    ! [A_29] : k10_relat_1(k6_relat_1(A_29),A_29) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_165])).

tff(c_244,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,k1_tarski(A_99)) != k1_xboole_0
      | ~ r2_hidden(A_99,k2_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_250,plain,(
    ! [A_29,A_99] :
      ( k10_relat_1(k6_relat_1(A_29),k1_tarski(A_99)) != k1_xboole_0
      | ~ r2_hidden(A_99,A_29)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_244])).

tff(c_270,plain,(
    ! [A_112,A_113] :
      ( k10_relat_1(k6_relat_1(A_112),k1_tarski(A_113)) != k1_xboole_0
      | ~ r2_hidden(A_113,A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_250])).

tff(c_277,plain,(
    ! [A_113] :
      ( k1_tarski(A_113) != k1_xboole_0
      | ~ r2_hidden(A_113,k1_tarski(A_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_270])).

tff(c_280,plain,(
    ! [A_113] : k1_tarski(A_113) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_277])).

tff(c_92,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_90,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_88,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_86,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_423,plain,(
    ! [D_151,C_152,B_153,A_154] :
      ( r2_hidden(k1_funct_1(D_151,C_152),B_153)
      | k1_xboole_0 = B_153
      | ~ r2_hidden(C_152,A_154)
      | ~ m1_subset_1(D_151,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153)))
      | ~ v1_funct_2(D_151,A_154,B_153)
      | ~ v1_funct_1(D_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_478,plain,(
    ! [D_155,B_156] :
      ( r2_hidden(k1_funct_1(D_155,'#skF_7'),B_156)
      | k1_xboole_0 = B_156
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_156)))
      | ~ v1_funct_2(D_155,'#skF_5',B_156)
      | ~ v1_funct_1(D_155) ) ),
    inference(resolution,[status(thm)],[c_86,c_423])).

tff(c_481,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_478])).

tff(c_484,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_481])).

tff(c_485,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_484])).

tff(c_28,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_281,plain,(
    ! [E_114,C_115,B_116,A_117] :
      ( E_114 = C_115
      | E_114 = B_116
      | E_114 = A_117
      | ~ r2_hidden(E_114,k1_enumset1(A_117,B_116,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_301,plain,(
    ! [E_119,B_120,A_121] :
      ( E_119 = B_120
      | E_119 = A_121
      | E_119 = A_121
      | ~ r2_hidden(E_119,k2_tarski(A_121,B_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_281])).

tff(c_310,plain,(
    ! [E_119,A_8] :
      ( E_119 = A_8
      | E_119 = A_8
      | E_119 = A_8
      | ~ r2_hidden(E_119,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_301])).

tff(c_490,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_485,c_310])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_84,c_490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:31:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1 > #skF_4
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.74/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.74/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.40  
% 2.74/1.41  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.74/1.41  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.74/1.41  tff(f_44, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.74/1.41  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.74/1.41  tff(f_71, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.74/1.41  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.74/1.41  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.74/1.41  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.74/1.41  tff(f_98, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.74/1.41  tff(c_84, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.74/1.41  tff(c_26, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.74/1.41  tff(c_124, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.41  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.41  tff(c_142, plain, (![B_51, A_52]: (r2_hidden(B_51, k2_tarski(A_52, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_4])).
% 2.74/1.41  tff(c_145, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_142])).
% 2.74/1.41  tff(c_70, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.41  tff(c_74, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_76, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.41  tff(c_156, plain, (![A_71]: (k10_relat_1(A_71, k2_relat_1(A_71))=k1_relat_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.74/1.41  tff(c_165, plain, (![A_29]: (k10_relat_1(k6_relat_1(A_29), A_29)=k1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_156])).
% 2.74/1.41  tff(c_169, plain, (![A_29]: (k10_relat_1(k6_relat_1(A_29), A_29)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_165])).
% 2.74/1.41  tff(c_244, plain, (![B_98, A_99]: (k10_relat_1(B_98, k1_tarski(A_99))!=k1_xboole_0 | ~r2_hidden(A_99, k2_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.74/1.41  tff(c_250, plain, (![A_29, A_99]: (k10_relat_1(k6_relat_1(A_29), k1_tarski(A_99))!=k1_xboole_0 | ~r2_hidden(A_99, A_29) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_244])).
% 2.74/1.41  tff(c_270, plain, (![A_112, A_113]: (k10_relat_1(k6_relat_1(A_112), k1_tarski(A_113))!=k1_xboole_0 | ~r2_hidden(A_113, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_250])).
% 2.74/1.41  tff(c_277, plain, (![A_113]: (k1_tarski(A_113)!=k1_xboole_0 | ~r2_hidden(A_113, k1_tarski(A_113)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_270])).
% 2.74/1.41  tff(c_280, plain, (![A_113]: (k1_tarski(A_113)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_277])).
% 2.74/1.41  tff(c_92, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.74/1.41  tff(c_90, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.74/1.41  tff(c_88, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.74/1.41  tff(c_86, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.74/1.41  tff(c_423, plain, (![D_151, C_152, B_153, A_154]: (r2_hidden(k1_funct_1(D_151, C_152), B_153) | k1_xboole_0=B_153 | ~r2_hidden(C_152, A_154) | ~m1_subset_1(D_151, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))) | ~v1_funct_2(D_151, A_154, B_153) | ~v1_funct_1(D_151))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.74/1.41  tff(c_478, plain, (![D_155, B_156]: (r2_hidden(k1_funct_1(D_155, '#skF_7'), B_156) | k1_xboole_0=B_156 | ~m1_subset_1(D_155, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_156))) | ~v1_funct_2(D_155, '#skF_5', B_156) | ~v1_funct_1(D_155))), inference(resolution, [status(thm)], [c_86, c_423])).
% 2.74/1.41  tff(c_481, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_88, c_478])).
% 2.74/1.41  tff(c_484, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_481])).
% 2.74/1.41  tff(c_485, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_280, c_484])).
% 2.74/1.41  tff(c_28, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.41  tff(c_281, plain, (![E_114, C_115, B_116, A_117]: (E_114=C_115 | E_114=B_116 | E_114=A_117 | ~r2_hidden(E_114, k1_enumset1(A_117, B_116, C_115)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.41  tff(c_301, plain, (![E_119, B_120, A_121]: (E_119=B_120 | E_119=A_121 | E_119=A_121 | ~r2_hidden(E_119, k2_tarski(A_121, B_120)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_281])).
% 2.74/1.41  tff(c_310, plain, (![E_119, A_8]: (E_119=A_8 | E_119=A_8 | E_119=A_8 | ~r2_hidden(E_119, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_301])).
% 2.74/1.41  tff(c_490, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_485, c_310])).
% 2.74/1.41  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_84, c_490])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 89
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 0
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 1
% 2.74/1.41  #Demod        : 16
% 2.74/1.41  #Tautology    : 44
% 2.74/1.41  #SimpNegUnit  : 2
% 2.74/1.41  #BackRed      : 0
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.42  Preprocessing        : 0.35
% 2.74/1.42  Parsing              : 0.17
% 2.74/1.42  CNF conversion       : 0.03
% 2.74/1.42  Main loop            : 0.30
% 2.74/1.42  Inferencing          : 0.10
% 2.74/1.42  Reduction            : 0.09
% 2.74/1.42  Demodulation         : 0.06
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.07
% 2.74/1.42  Abstraction          : 0.03
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.67
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
