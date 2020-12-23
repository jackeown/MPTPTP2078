%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   69 (  78 expanded)
%              Number of leaves         :   36 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 (  81 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_84,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_298,plain,(
    ! [C_169,E_166,A_167,D_168,B_165] : k4_enumset1(A_167,A_167,B_165,C_169,D_168,E_166) = k3_enumset1(A_167,B_165,C_169,D_168,E_166) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [C_39,B_38,H_46,A_37,D_40,F_42] : r2_hidden(H_46,k4_enumset1(A_37,B_38,C_39,D_40,H_46,F_42)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_343,plain,(
    ! [C_171,D_173,E_174,A_172,B_170] : r2_hidden(D_173,k3_enumset1(A_172,B_170,C_171,D_173,E_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_30])).

tff(c_358,plain,(
    ! [C_175,A_176,B_177,D_178] : r2_hidden(C_175,k2_enumset1(A_176,B_177,C_175,D_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_343])).

tff(c_373,plain,(
    ! [B_179,A_180,C_181] : r2_hidden(B_179,k1_enumset1(A_180,B_179,C_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_358])).

tff(c_397,plain,(
    ! [A_188,B_189] : r2_hidden(A_188,k2_tarski(A_188,B_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_373])).

tff(c_412,plain,(
    ! [A_190] : r2_hidden(A_190,k1_tarski(A_190)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_397])).

tff(c_76,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_423,plain,(
    ! [A_190] : ~ r1_tarski(k1_tarski(A_190),A_190) ),
    inference(resolution,[status(thm)],[c_412,c_76])).

tff(c_78,plain,(
    k1_ordinal1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_74,plain,(
    ! [A_51] : k2_xboole_0(A_51,k1_tarski(A_51)) = k1_ordinal1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_104,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_36] : r1_tarski(A_36,k1_zfmisc_1(k3_tarski(A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_184,plain,(
    ! [A_82,B_83] : r1_tarski(k2_tarski(A_82,B_83),k1_zfmisc_1(k2_xboole_0(A_82,B_83))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_24])).

tff(c_212,plain,(
    ! [A_94] : r1_tarski(k2_tarski(A_94,k1_tarski(A_94)),k1_zfmisc_1(k1_ordinal1(A_94))) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_184])).

tff(c_215,plain,(
    r1_tarski(k2_tarski('#skF_4',k1_tarski('#skF_4')),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_212])).

tff(c_28,plain,(
    ! [C_39,B_38,H_46,A_37,D_40,E_41] : r2_hidden(H_46,k4_enumset1(A_37,B_38,C_39,D_40,E_41,H_46)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_697,plain,(
    ! [C_312,B_311,D_314,E_315,A_313] : r2_hidden(E_315,k3_enumset1(A_313,B_311,C_312,D_314,E_315)) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_28])).

tff(c_712,plain,(
    ! [D_316,A_317,B_318,C_319] : r2_hidden(D_316,k2_enumset1(A_317,B_318,C_319,D_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_697])).

tff(c_727,plain,(
    ! [C_320,A_321,B_322] : r2_hidden(C_320,k1_enumset1(A_321,B_322,C_320)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_712])).

tff(c_759,plain,(
    ! [B_330,A_331] : r2_hidden(B_330,k2_tarski(A_331,B_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_727])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1721,plain,(
    ! [B_579,B_580,A_581] :
      ( r2_hidden(B_579,B_580)
      | ~ r1_tarski(k2_tarski(A_581,B_579),B_580) ) ),
    inference(resolution,[status(thm)],[c_759,c_2])).

tff(c_1757,plain,(
    r2_hidden(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_215,c_1721])).

tff(c_68,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1773,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1757,c_68])).

tff(c_70,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1777,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1773,c_70])).

tff(c_1781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_1777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.85  
% 4.67/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.85  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 4.67/1.85  
% 4.67/1.85  %Foreground sorts:
% 4.67/1.85  
% 4.67/1.85  
% 4.67/1.85  %Background operators:
% 4.67/1.85  
% 4.67/1.85  
% 4.67/1.85  %Foreground operators:
% 4.67/1.85  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.67/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.67/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.67/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.67/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.67/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.67/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.67/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.67/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.85  
% 4.67/1.87  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.67/1.87  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.67/1.87  tff(f_38, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.67/1.87  tff(f_40, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.67/1.87  tff(f_42, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.67/1.87  tff(f_74, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 4.67/1.87  tff(f_89, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.67/1.87  tff(f_93, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 4.67/1.87  tff(f_84, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.67/1.87  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.67/1.87  tff(f_50, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 4.67/1.87  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.67/1.87  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.67/1.87  tff(f_82, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.67/1.87  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.67/1.87  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.67/1.87  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.67/1.87  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.67/1.87  tff(c_298, plain, (![C_169, E_166, A_167, D_168, B_165]: (k4_enumset1(A_167, A_167, B_165, C_169, D_168, E_166)=k3_enumset1(A_167, B_165, C_169, D_168, E_166))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.67/1.87  tff(c_30, plain, (![C_39, B_38, H_46, A_37, D_40, F_42]: (r2_hidden(H_46, k4_enumset1(A_37, B_38, C_39, D_40, H_46, F_42)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.67/1.87  tff(c_343, plain, (![C_171, D_173, E_174, A_172, B_170]: (r2_hidden(D_173, k3_enumset1(A_172, B_170, C_171, D_173, E_174)))), inference(superposition, [status(thm), theory('equality')], [c_298, c_30])).
% 4.67/1.87  tff(c_358, plain, (![C_175, A_176, B_177, D_178]: (r2_hidden(C_175, k2_enumset1(A_176, B_177, C_175, D_178)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_343])).
% 4.67/1.87  tff(c_373, plain, (![B_179, A_180, C_181]: (r2_hidden(B_179, k1_enumset1(A_180, B_179, C_181)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_358])).
% 4.67/1.87  tff(c_397, plain, (![A_188, B_189]: (r2_hidden(A_188, k2_tarski(A_188, B_189)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_373])).
% 4.67/1.87  tff(c_412, plain, (![A_190]: (r2_hidden(A_190, k1_tarski(A_190)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_397])).
% 4.67/1.87  tff(c_76, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.67/1.87  tff(c_423, plain, (![A_190]: (~r1_tarski(k1_tarski(A_190), A_190))), inference(resolution, [status(thm)], [c_412, c_76])).
% 4.67/1.87  tff(c_78, plain, (k1_ordinal1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.67/1.87  tff(c_74, plain, (![A_51]: (k2_xboole_0(A_51, k1_tarski(A_51))=k1_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.67/1.87  tff(c_104, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.67/1.87  tff(c_24, plain, (![A_36]: (r1_tarski(A_36, k1_zfmisc_1(k3_tarski(A_36))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.67/1.87  tff(c_184, plain, (![A_82, B_83]: (r1_tarski(k2_tarski(A_82, B_83), k1_zfmisc_1(k2_xboole_0(A_82, B_83))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_24])).
% 4.67/1.87  tff(c_212, plain, (![A_94]: (r1_tarski(k2_tarski(A_94, k1_tarski(A_94)), k1_zfmisc_1(k1_ordinal1(A_94))))), inference(superposition, [status(thm), theory('equality')], [c_74, c_184])).
% 4.67/1.87  tff(c_215, plain, (r1_tarski(k2_tarski('#skF_4', k1_tarski('#skF_4')), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_212])).
% 4.67/1.87  tff(c_28, plain, (![C_39, B_38, H_46, A_37, D_40, E_41]: (r2_hidden(H_46, k4_enumset1(A_37, B_38, C_39, D_40, E_41, H_46)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.67/1.87  tff(c_697, plain, (![C_312, B_311, D_314, E_315, A_313]: (r2_hidden(E_315, k3_enumset1(A_313, B_311, C_312, D_314, E_315)))), inference(superposition, [status(thm), theory('equality')], [c_298, c_28])).
% 4.67/1.87  tff(c_712, plain, (![D_316, A_317, B_318, C_319]: (r2_hidden(D_316, k2_enumset1(A_317, B_318, C_319, D_316)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_697])).
% 4.67/1.87  tff(c_727, plain, (![C_320, A_321, B_322]: (r2_hidden(C_320, k1_enumset1(A_321, B_322, C_320)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_712])).
% 4.67/1.87  tff(c_759, plain, (![B_330, A_331]: (r2_hidden(B_330, k2_tarski(A_331, B_330)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_727])).
% 4.67/1.87  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.67/1.87  tff(c_1721, plain, (![B_579, B_580, A_581]: (r2_hidden(B_579, B_580) | ~r1_tarski(k2_tarski(A_581, B_579), B_580))), inference(resolution, [status(thm)], [c_759, c_2])).
% 4.67/1.87  tff(c_1757, plain, (r2_hidden(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_215, c_1721])).
% 4.67/1.87  tff(c_68, plain, (![A_47, B_48]: (m1_subset_1(A_47, B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.67/1.87  tff(c_1773, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_1757, c_68])).
% 4.67/1.87  tff(c_70, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.67/1.87  tff(c_1777, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1773, c_70])).
% 4.67/1.87  tff(c_1781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_423, c_1777])).
% 4.67/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.87  
% 4.67/1.87  Inference rules
% 4.67/1.87  ----------------------
% 4.67/1.87  #Ref     : 0
% 4.67/1.87  #Sup     : 387
% 4.67/1.87  #Fact    : 0
% 4.67/1.87  #Define  : 0
% 4.67/1.87  #Split   : 0
% 4.67/1.87  #Chain   : 0
% 4.67/1.87  #Close   : 0
% 4.67/1.87  
% 4.67/1.87  Ordering : KBO
% 4.67/1.87  
% 4.67/1.87  Simplification rules
% 4.67/1.87  ----------------------
% 4.67/1.87  #Subsume      : 42
% 4.67/1.87  #Demod        : 92
% 4.67/1.87  #Tautology    : 118
% 4.67/1.87  #SimpNegUnit  : 1
% 4.67/1.87  #BackRed      : 0
% 4.67/1.87  
% 4.67/1.87  #Partial instantiations: 0
% 4.67/1.87  #Strategies tried      : 1
% 4.67/1.87  
% 4.67/1.87  Timing (in seconds)
% 4.67/1.87  ----------------------
% 4.67/1.87  Preprocessing        : 0.35
% 4.67/1.87  Parsing              : 0.17
% 4.67/1.87  CNF conversion       : 0.03
% 4.67/1.87  Main loop            : 0.74
% 4.67/1.87  Inferencing          : 0.26
% 4.67/1.87  Reduction            : 0.24
% 4.67/1.87  Demodulation         : 0.18
% 4.67/1.87  BG Simplification    : 0.03
% 4.67/1.87  Subsumption          : 0.16
% 4.67/1.87  Abstraction          : 0.04
% 4.67/1.87  MUC search           : 0.00
% 4.67/1.87  Cooper               : 0.00
% 4.67/1.87  Total                : 1.12
% 4.67/1.87  Index Insertion      : 0.00
% 4.67/1.87  Index Deletion       : 0.00
% 4.67/1.87  Index Matching       : 0.00
% 4.67/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
