%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:36 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 177 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  102 ( 346 expanded)
%              Number of equality atoms :   31 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_67,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_77,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_88,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_44])).

tff(c_78,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [B_27,A_26] :
      ( r1_xboole_0(B_27,k1_tarski(A_26))
      | r2_hidden(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_94,plain,(
    ! [B_36,A_37] :
      ( k10_relat_1(B_36,A_37) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_196,plain,(
    ! [B_54,A_55] :
      ( k10_relat_1(B_54,k1_tarski(A_55)) = k1_xboole_0
      | ~ v1_relat_1(B_54)
      | r2_hidden(A_55,k2_relat_1(B_54)) ) ),
    inference(resolution,[status(thm)],[c_81,c_94])).

tff(c_199,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_77])).

tff(c_205,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_205])).

tff(c_208,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_209,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_283,plain,(
    ! [B_73,A_74] :
      ( k10_relat_1(B_73,A_74) != k1_xboole_0
      | ~ r1_tarski(A_74,k2_relat_1(B_73))
      | k1_xboole_0 = A_74
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_340,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(B_89,k1_tarski(A_90)) != k1_xboole_0
      | k1_tarski(A_90) = k1_xboole_0
      | ~ v1_relat_1(B_89)
      | ~ r2_hidden(A_90,k2_relat_1(B_89)) ) ),
    inference(resolution,[status(thm)],[c_16,c_283])).

tff(c_346,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | k1_tarski('#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_209,c_340])).

tff(c_353,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_208,c_346])).

tff(c_12,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | k3_xboole_0(A_9,k1_tarski(B_10)) != k1_tarski(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_361,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1',A_9)
      | k3_xboole_0(A_9,k1_xboole_0) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_18])).

tff(c_377,plain,(
    ! [A_9] : r2_hidden('#skF_1',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_12,c_361])).

tff(c_382,plain,(
    ! [A_91] : r2_hidden('#skF_1',A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_12,c_361])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ r2_hidden(C_5,B_4)
      | ~ r2_hidden(C_5,A_3)
      | ~ r2_hidden(C_5,k2_xboole_0(A_3,B_4))
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_390,plain,(
    ! [B_4,A_3] :
      ( ~ r2_hidden('#skF_1',B_4)
      | ~ r2_hidden('#skF_1',A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_382,c_4])).

tff(c_403,plain,(
    ! [A_3,B_4] : ~ r1_xboole_0(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_377,c_390])).

tff(c_68,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k3_xboole_0(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_68])).

tff(c_72,plain,(
    ! [A_6] : ~ v1_relat_1(A_6) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_36])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_24,plain,(
    ! [A_15] : k10_relat_1(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_231,plain,(
    ! [B_66,A_67] :
      ( r1_xboole_0(k2_relat_1(B_66),A_67)
      | k10_relat_1(B_66,A_67) != k1_xboole_0
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_236,plain,(
    ! [A_67] :
      ( r1_xboole_0(k1_xboole_0,A_67)
      | k10_relat_1(k1_xboole_0,A_67) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_231])).

tff(c_240,plain,(
    ! [A_68] : r1_xboole_0(k1_xboole_0,A_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24,c_236])).

tff(c_243,plain,(
    ! [A_68] : r1_xboole_0(A_68,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_240,c_2])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_403,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.39/1.31  
% 2.39/1.31  %Foreground sorts:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Background operators:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Foreground operators:
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.31  
% 2.39/1.34  tff(f_94, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.39/1.34  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 2.39/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.39/1.34  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.39/1.34  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.39/1.34  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.39/1.34  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.39/1.34  tff(f_56, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.39/1.34  tff(f_46, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 2.39/1.34  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.39/1.34  tff(f_67, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.39/1.34  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.39/1.34  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.39/1.34  tff(c_38, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.39/1.34  tff(c_77, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.39/1.34  tff(c_44, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.39/1.34  tff(c_88, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_77, c_44])).
% 2.39/1.34  tff(c_78, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.39/1.34  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.34  tff(c_81, plain, (![B_27, A_26]: (r1_xboole_0(B_27, k1_tarski(A_26)) | r2_hidden(A_26, B_27))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.39/1.34  tff(c_94, plain, (![B_36, A_37]: (k10_relat_1(B_36, A_37)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.34  tff(c_196, plain, (![B_54, A_55]: (k10_relat_1(B_54, k1_tarski(A_55))=k1_xboole_0 | ~v1_relat_1(B_54) | r2_hidden(A_55, k2_relat_1(B_54)))), inference(resolution, [status(thm)], [c_81, c_94])).
% 2.39/1.34  tff(c_199, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_196, c_77])).
% 2.39/1.34  tff(c_205, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199])).
% 2.39/1.34  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_205])).
% 2.39/1.34  tff(c_208, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.39/1.34  tff(c_209, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.39/1.34  tff(c_16, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.34  tff(c_283, plain, (![B_73, A_74]: (k10_relat_1(B_73, A_74)!=k1_xboole_0 | ~r1_tarski(A_74, k2_relat_1(B_73)) | k1_xboole_0=A_74 | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.39/1.34  tff(c_340, plain, (![B_89, A_90]: (k10_relat_1(B_89, k1_tarski(A_90))!=k1_xboole_0 | k1_tarski(A_90)=k1_xboole_0 | ~v1_relat_1(B_89) | ~r2_hidden(A_90, k2_relat_1(B_89)))), inference(resolution, [status(thm)], [c_16, c_283])).
% 2.39/1.34  tff(c_346, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | k1_tarski('#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_209, c_340])).
% 2.39/1.34  tff(c_353, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_208, c_346])).
% 2.39/1.34  tff(c_12, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.39/1.34  tff(c_18, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | k3_xboole_0(A_9, k1_tarski(B_10))!=k1_tarski(B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.39/1.34  tff(c_361, plain, (![A_9]: (r2_hidden('#skF_1', A_9) | k3_xboole_0(A_9, k1_xboole_0)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_18])).
% 2.39/1.34  tff(c_377, plain, (![A_9]: (r2_hidden('#skF_1', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_12, c_361])).
% 2.39/1.34  tff(c_382, plain, (![A_91]: (r2_hidden('#skF_1', A_91))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_12, c_361])).
% 2.39/1.34  tff(c_4, plain, (![C_5, B_4, A_3]: (~r2_hidden(C_5, B_4) | ~r2_hidden(C_5, A_3) | ~r2_hidden(C_5, k2_xboole_0(A_3, B_4)) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.39/1.34  tff(c_390, plain, (![B_4, A_3]: (~r2_hidden('#skF_1', B_4) | ~r2_hidden('#skF_1', A_3) | ~r1_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_382, c_4])).
% 2.39/1.34  tff(c_403, plain, (![A_3, B_4]: (~r1_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_377, c_390])).
% 2.39/1.34  tff(c_68, plain, (![A_24, B_25]: (v1_relat_1(k3_xboole_0(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.39/1.34  tff(c_71, plain, (![A_6]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_68])).
% 2.39/1.34  tff(c_72, plain, (![A_6]: (~v1_relat_1(A_6))), inference(splitLeft, [status(thm)], [c_71])).
% 2.39/1.34  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_36])).
% 2.39/1.34  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_71])).
% 2.39/1.34  tff(c_24, plain, (![A_15]: (k10_relat_1(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.34  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.39/1.34  tff(c_231, plain, (![B_66, A_67]: (r1_xboole_0(k2_relat_1(B_66), A_67) | k10_relat_1(B_66, A_67)!=k1_xboole_0 | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.39/1.34  tff(c_236, plain, (![A_67]: (r1_xboole_0(k1_xboole_0, A_67) | k10_relat_1(k1_xboole_0, A_67)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_231])).
% 2.39/1.34  tff(c_240, plain, (![A_68]: (r1_xboole_0(k1_xboole_0, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24, c_236])).
% 2.39/1.34  tff(c_243, plain, (![A_68]: (r1_xboole_0(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_240, c_2])).
% 2.39/1.34  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_403, c_243])).
% 2.39/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  Inference rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Ref     : 0
% 2.39/1.34  #Sup     : 78
% 2.39/1.34  #Fact    : 0
% 2.39/1.34  #Define  : 0
% 2.39/1.34  #Split   : 2
% 2.39/1.34  #Chain   : 0
% 2.39/1.34  #Close   : 0
% 2.39/1.34  
% 2.39/1.34  Ordering : KBO
% 2.39/1.34  
% 2.39/1.34  Simplification rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Subsume      : 10
% 2.39/1.34  #Demod        : 48
% 2.39/1.34  #Tautology    : 48
% 2.39/1.34  #SimpNegUnit  : 11
% 2.39/1.34  #BackRed      : 8
% 2.39/1.34  
% 2.39/1.34  #Partial instantiations: 0
% 2.39/1.34  #Strategies tried      : 1
% 2.39/1.34  
% 2.39/1.34  Timing (in seconds)
% 2.39/1.34  ----------------------
% 2.39/1.35  Preprocessing        : 0.29
% 2.39/1.35  Parsing              : 0.16
% 2.39/1.35  CNF conversion       : 0.02
% 2.39/1.35  Main loop            : 0.26
% 2.39/1.35  Inferencing          : 0.11
% 2.39/1.35  Reduction            : 0.07
% 2.39/1.35  Demodulation         : 0.05
% 2.39/1.35  BG Simplification    : 0.01
% 2.39/1.35  Subsumption          : 0.05
% 2.39/1.35  Abstraction          : 0.01
% 2.39/1.35  MUC search           : 0.00
% 2.39/1.35  Cooper               : 0.00
% 2.39/1.35  Total                : 0.60
% 2.39/1.35  Index Insertion      : 0.00
% 2.39/1.35  Index Deletion       : 0.00
% 2.39/1.35  Index Matching       : 0.00
% 2.39/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
