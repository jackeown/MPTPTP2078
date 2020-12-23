%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :   80 (  91 expanded)
%              Number of leaves         :   45 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 113 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_97,axiom,(
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

tff(c_106,plain,
    ( k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_157,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_112,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | k10_relat_1('#skF_12',k1_tarski('#skF_11')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_236,plain,(
    k10_relat_1('#skF_12',k1_tarski('#skF_11')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_112])).

tff(c_104,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_189,plain,(
    ! [A_131,B_132] :
      ( r1_xboole_0(k1_tarski(A_131),B_132)
      | r2_hidden(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_196,plain,(
    ! [B_132,A_131] :
      ( r1_xboole_0(B_132,k1_tarski(A_131))
      | r2_hidden(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_420,plain,(
    ! [B_182,A_183] :
      ( k10_relat_1(B_182,A_183) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_182),A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1738,plain,(
    ! [B_396,A_397] :
      ( k10_relat_1(B_396,k1_tarski(A_397)) = k1_xboole_0
      | ~ v1_relat_1(B_396)
      | r2_hidden(A_397,k2_relat_1(B_396)) ) ),
    inference(resolution,[status(thm)],[c_196,c_420])).

tff(c_1779,plain,
    ( k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1738,c_157])).

tff(c_1805,plain,(
    k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1779])).

tff(c_1807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1805])).

tff(c_1809,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_88,plain,(
    ! [A_92,C_107] :
      ( r2_hidden(k4_tarski('#skF_10'(A_92,k2_relat_1(A_92),C_107),C_107),A_92)
      | ~ r2_hidden(C_107,k2_relat_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,(
    ! [A_115,B_116] : ~ r2_hidden(A_115,k2_zfmisc_1(A_115,B_116)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_135])).

tff(c_1808,plain,(
    k10_relat_1('#skF_12',k1_tarski('#skF_11')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2132,plain,(
    ! [A_463,B_464,C_465,D_466] : k3_enumset1(A_463,A_463,B_464,C_465,D_466) = k2_enumset1(A_463,B_464,C_465,D_466) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    ! [G_49,D_44,C_43,A_41,E_45] : r2_hidden(G_49,k3_enumset1(A_41,G_49,C_43,D_44,E_45)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2156,plain,(
    ! [A_467,B_468,C_469,D_470] : r2_hidden(A_467,k2_enumset1(A_467,B_468,C_469,D_470)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2132,c_42])).

tff(c_2187,plain,(
    ! [A_475,B_476,C_477] : r2_hidden(A_475,k1_enumset1(A_475,B_476,C_477)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2156])).

tff(c_2197,plain,(
    ! [A_480,B_481] : r2_hidden(A_480,k2_tarski(A_480,B_481)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2187])).

tff(c_2204,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2197])).

tff(c_2309,plain,(
    ! [D_518,A_519,B_520,E_521] :
      ( r2_hidden(D_518,k10_relat_1(A_519,B_520))
      | ~ r2_hidden(E_521,B_520)
      | ~ r2_hidden(k4_tarski(D_518,E_521),A_519)
      | ~ v1_relat_1(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5829,plain,(
    ! [D_807,A_808,A_809] :
      ( r2_hidden(D_807,k10_relat_1(A_808,k1_tarski(A_809)))
      | ~ r2_hidden(k4_tarski(D_807,A_809),A_808)
      | ~ v1_relat_1(A_808) ) ),
    inference(resolution,[status(thm)],[c_2204,c_2309])).

tff(c_5894,plain,(
    ! [D_807] :
      ( r2_hidden(D_807,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_807,'#skF_11'),'#skF_12')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1808,c_5829])).

tff(c_5916,plain,(
    ! [D_807] :
      ( r2_hidden(D_807,k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_807,'#skF_11'),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5894])).

tff(c_5934,plain,(
    ! [D_816] : ~ r2_hidden(k4_tarski(D_816,'#skF_11'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_5916])).

tff(c_5938,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_88,c_5934])).

tff(c_5942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1809,c_5938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.55  
% 7.16/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.55  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1 > #skF_11 > #skF_4 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 7.16/2.55  
% 7.16/2.55  %Foreground sorts:
% 7.16/2.55  
% 7.16/2.55  
% 7.16/2.55  %Background operators:
% 7.16/2.55  
% 7.16/2.55  
% 7.16/2.55  %Foreground operators:
% 7.16/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.55  tff('#skF_11', type, '#skF_11': $i).
% 7.16/2.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.16/2.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.16/2.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.16/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.16/2.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.16/2.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.16/2.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.16/2.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.16/2.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.16/2.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.16/2.55  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.16/2.55  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.16/2.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.55  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.16/2.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.16/2.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.16/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.55  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.16/2.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.55  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.16/2.55  tff('#skF_12', type, '#skF_12': $i).
% 7.16/2.55  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 7.16/2.55  
% 7.36/2.56  tff(f_119, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 7.36/2.56  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.36/2.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.36/2.56  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 7.36/2.56  tff(f_105, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 7.36/2.56  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.36/2.57  tff(f_63, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 7.36/2.57  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.36/2.57  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.36/2.57  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.36/2.57  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 7.36/2.57  tff(f_84, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 7.36/2.57  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 7.36/2.57  tff(c_106, plain, (k10_relat_1('#skF_12', k1_tarski('#skF_11'))=k1_xboole_0 | ~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.36/2.57  tff(c_157, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_106])).
% 7.36/2.57  tff(c_112, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12')) | k10_relat_1('#skF_12', k1_tarski('#skF_11'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.36/2.57  tff(c_236, plain, (k10_relat_1('#skF_12', k1_tarski('#skF_11'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_157, c_112])).
% 7.36/2.57  tff(c_104, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.36/2.57  tff(c_189, plain, (![A_131, B_132]: (r1_xboole_0(k1_tarski(A_131), B_132) | r2_hidden(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.36/2.57  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.36/2.57  tff(c_196, plain, (![B_132, A_131]: (r1_xboole_0(B_132, k1_tarski(A_131)) | r2_hidden(A_131, B_132))), inference(resolution, [status(thm)], [c_189, c_2])).
% 7.36/2.57  tff(c_420, plain, (![B_182, A_183]: (k10_relat_1(B_182, A_183)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_182), A_183) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.36/2.57  tff(c_1738, plain, (![B_396, A_397]: (k10_relat_1(B_396, k1_tarski(A_397))=k1_xboole_0 | ~v1_relat_1(B_396) | r2_hidden(A_397, k2_relat_1(B_396)))), inference(resolution, [status(thm)], [c_196, c_420])).
% 7.36/2.57  tff(c_1779, plain, (k10_relat_1('#skF_12', k1_tarski('#skF_11'))=k1_xboole_0 | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_1738, c_157])).
% 7.36/2.57  tff(c_1805, plain, (k10_relat_1('#skF_12', k1_tarski('#skF_11'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1779])).
% 7.36/2.57  tff(c_1807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_1805])).
% 7.36/2.57  tff(c_1809, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_106])).
% 7.36/2.57  tff(c_88, plain, (![A_92, C_107]: (r2_hidden(k4_tarski('#skF_10'(A_92, k2_relat_1(A_92), C_107), C_107), A_92) | ~r2_hidden(C_107, k2_relat_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.36/2.57  tff(c_28, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.36/2.57  tff(c_135, plain, (![A_115, B_116]: (~r2_hidden(A_115, k2_zfmisc_1(A_115, B_116)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.36/2.57  tff(c_138, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_135])).
% 7.36/2.57  tff(c_1808, plain, (k10_relat_1('#skF_12', k1_tarski('#skF_11'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 7.36/2.57  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.36/2.57  tff(c_12, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.36/2.57  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.36/2.57  tff(c_2132, plain, (![A_463, B_464, C_465, D_466]: (k3_enumset1(A_463, A_463, B_464, C_465, D_466)=k2_enumset1(A_463, B_464, C_465, D_466))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.36/2.57  tff(c_42, plain, (![G_49, D_44, C_43, A_41, E_45]: (r2_hidden(G_49, k3_enumset1(A_41, G_49, C_43, D_44, E_45)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.36/2.57  tff(c_2156, plain, (![A_467, B_468, C_469, D_470]: (r2_hidden(A_467, k2_enumset1(A_467, B_468, C_469, D_470)))), inference(superposition, [status(thm), theory('equality')], [c_2132, c_42])).
% 7.36/2.57  tff(c_2187, plain, (![A_475, B_476, C_477]: (r2_hidden(A_475, k1_enumset1(A_475, B_476, C_477)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2156])).
% 7.36/2.57  tff(c_2197, plain, (![A_480, B_481]: (r2_hidden(A_480, k2_tarski(A_480, B_481)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2187])).
% 7.36/2.57  tff(c_2204, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2197])).
% 7.36/2.57  tff(c_2309, plain, (![D_518, A_519, B_520, E_521]: (r2_hidden(D_518, k10_relat_1(A_519, B_520)) | ~r2_hidden(E_521, B_520) | ~r2_hidden(k4_tarski(D_518, E_521), A_519) | ~v1_relat_1(A_519))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.36/2.57  tff(c_5829, plain, (![D_807, A_808, A_809]: (r2_hidden(D_807, k10_relat_1(A_808, k1_tarski(A_809))) | ~r2_hidden(k4_tarski(D_807, A_809), A_808) | ~v1_relat_1(A_808))), inference(resolution, [status(thm)], [c_2204, c_2309])).
% 7.36/2.57  tff(c_5894, plain, (![D_807]: (r2_hidden(D_807, k1_xboole_0) | ~r2_hidden(k4_tarski(D_807, '#skF_11'), '#skF_12') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1808, c_5829])).
% 7.36/2.57  tff(c_5916, plain, (![D_807]: (r2_hidden(D_807, k1_xboole_0) | ~r2_hidden(k4_tarski(D_807, '#skF_11'), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5894])).
% 7.36/2.57  tff(c_5934, plain, (![D_816]: (~r2_hidden(k4_tarski(D_816, '#skF_11'), '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_138, c_5916])).
% 7.36/2.57  tff(c_5938, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_88, c_5934])).
% 7.36/2.57  tff(c_5942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1809, c_5938])).
% 7.36/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.57  
% 7.36/2.57  Inference rules
% 7.36/2.57  ----------------------
% 7.36/2.57  #Ref     : 0
% 7.36/2.57  #Sup     : 1325
% 7.36/2.57  #Fact    : 0
% 7.36/2.57  #Define  : 0
% 7.36/2.57  #Split   : 3
% 7.36/2.57  #Chain   : 0
% 7.36/2.57  #Close   : 0
% 7.36/2.57  
% 7.36/2.57  Ordering : KBO
% 7.36/2.57  
% 7.36/2.57  Simplification rules
% 7.36/2.57  ----------------------
% 7.36/2.57  #Subsume      : 222
% 7.36/2.57  #Demod        : 418
% 7.36/2.57  #Tautology    : 257
% 7.36/2.57  #SimpNegUnit  : 16
% 7.36/2.57  #BackRed      : 24
% 7.36/2.57  
% 7.36/2.57  #Partial instantiations: 0
% 7.36/2.57  #Strategies tried      : 1
% 7.36/2.57  
% 7.36/2.57  Timing (in seconds)
% 7.36/2.57  ----------------------
% 7.36/2.57  Preprocessing        : 0.39
% 7.36/2.57  Parsing              : 0.18
% 7.36/2.57  CNF conversion       : 0.04
% 7.36/2.57  Main loop            : 1.42
% 7.36/2.57  Inferencing          : 0.45
% 7.36/2.57  Reduction            : 0.49
% 7.36/2.57  Demodulation         : 0.37
% 7.36/2.57  BG Simplification    : 0.06
% 7.36/2.57  Subsumption          : 0.30
% 7.36/2.57  Abstraction          : 0.08
% 7.36/2.57  MUC search           : 0.00
% 7.36/2.57  Cooper               : 0.00
% 7.36/2.57  Total                : 1.83
% 7.36/2.57  Index Insertion      : 0.00
% 7.36/2.57  Index Deletion       : 0.00
% 7.36/2.57  Index Matching       : 0.00
% 7.36/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
