%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:52 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 113 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 173 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_70,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

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

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_48,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_2'),'#skF_4')
    | k1_mcart_1('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_81,plain,(
    k1_mcart_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    r2_hidden('#skF_2',k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_317,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(k1_mcart_1(A_103),B_104)
      | ~ r2_hidden(A_103,k2_zfmisc_1(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_328,plain,(
    r2_hidden(k1_mcart_1('#skF_2'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_317])).

tff(c_30,plain,(
    ! [A_32] : k3_tarski(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [A_46] : r1_tarski(A_46,k1_zfmisc_1(k3_tarski(A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    ! [A_32] : r1_tarski(k1_tarski(A_32),k1_zfmisc_1(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_71])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    ! [A_67,C_68,B_69] :
      ( r2_hidden(A_67,C_68)
      | ~ r1_tarski(k2_tarski(A_67,B_69),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_164,plain,(
    ! [A_76,C_77] :
      ( r2_hidden(A_76,C_77)
      | ~ r1_tarski(k1_tarski(A_76),C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_131])).

tff(c_176,plain,(
    ! [A_32] : r2_hidden(A_32,k1_zfmisc_1(A_32)) ),
    inference(resolution,[status(thm)],[c_74,c_164])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(k1_tarski(A_29),B_30)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_270,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,B_95)
      | ~ r2_hidden(C_96,A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_516,plain,(
    ! [C_155,B_156,A_157] :
      ( ~ r2_hidden(C_155,B_156)
      | ~ r2_hidden(C_155,k1_tarski(A_157))
      | r2_hidden(A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_26,c_270])).

tff(c_625,plain,(
    ! [A_167,A_168] :
      ( ~ r2_hidden(A_167,k1_tarski(A_168))
      | r2_hidden(A_168,k1_zfmisc_1(A_167)) ) ),
    inference(resolution,[status(thm)],[c_176,c_516])).

tff(c_639,plain,(
    r2_hidden('#skF_3',k1_zfmisc_1(k1_mcart_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_328,c_625])).

tff(c_38,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_650,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_mcart_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_639,c_38])).

tff(c_40,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_661,plain,(
    r1_tarski('#skF_3',k1_mcart_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_650,c_40])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_672,plain,
    ( k1_mcart_1('#skF_2') = '#skF_3'
    | ~ r1_tarski(k1_mcart_1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_661,c_8])).

tff(c_675,plain,(
    ~ r1_tarski(k1_mcart_1('#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_672])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [B_60,C_61,A_62] :
      ( r2_hidden(B_60,C_61)
      | ~ r1_tarski(k2_tarski(A_62,B_60),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_117,plain,(
    ! [B_63,A_64] : r2_hidden(B_63,k2_tarski(A_64,B_63)) ),
    inference(resolution,[status(thm)],[c_12,c_103])).

tff(c_123,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_584,plain,(
    ! [A_164,A_165] :
      ( ~ r2_hidden(A_164,k1_tarski(A_165))
      | r2_hidden(A_165,k1_tarski(A_164)) ) ),
    inference(resolution,[status(thm)],[c_123,c_516])).

tff(c_595,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_mcart_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_328,c_584])).

tff(c_638,plain,(
    r2_hidden(k1_mcart_1('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_595,c_625])).

tff(c_657,plain,(
    m1_subset_1(k1_mcart_1('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_638,c_38])).

tff(c_678,plain,(
    r1_tarski(k1_mcart_1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_657,c_40])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_675,c_678])).

tff(c_683,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_881,plain,(
    ! [A_220,C_221,B_222] :
      ( r2_hidden(k2_mcart_1(A_220),C_221)
      | ~ r2_hidden(A_220,k2_zfmisc_1(B_222,C_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_889,plain,(
    r2_hidden(k2_mcart_1('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_881])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.48  
% 2.98/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.49  
% 2.98/1.49  %Foreground sorts:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Background operators:
% 2.98/1.49  
% 2.98/1.49  
% 2.98/1.49  %Foreground operators:
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.98/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.49  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.98/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.98/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.49  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.98/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.49  
% 3.06/1.50  tff(f_97, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 3.06/1.50  tff(f_90, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.06/1.50  tff(f_70, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.06/1.50  tff(f_68, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.06/1.50  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.06/1.50  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.06/1.50  tff(f_66, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.06/1.50  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.06/1.50  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.06/1.50  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.50  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.50  tff(c_48, plain, (~r2_hidden(k2_mcart_1('#skF_2'), '#skF_4') | k1_mcart_1('#skF_2')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.06/1.50  tff(c_81, plain, (k1_mcart_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 3.06/1.50  tff(c_50, plain, (r2_hidden('#skF_2', k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.06/1.50  tff(c_317, plain, (![A_103, B_104, C_105]: (r2_hidden(k1_mcart_1(A_103), B_104) | ~r2_hidden(A_103, k2_zfmisc_1(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.50  tff(c_328, plain, (r2_hidden(k1_mcart_1('#skF_2'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_317])).
% 3.06/1.50  tff(c_30, plain, (![A_32]: (k3_tarski(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.06/1.50  tff(c_71, plain, (![A_46]: (r1_tarski(A_46, k1_zfmisc_1(k3_tarski(A_46))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.06/1.50  tff(c_74, plain, (![A_32]: (r1_tarski(k1_tarski(A_32), k1_zfmisc_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_71])).
% 3.06/1.50  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.06/1.50  tff(c_131, plain, (![A_67, C_68, B_69]: (r2_hidden(A_67, C_68) | ~r1_tarski(k2_tarski(A_67, B_69), C_68))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.06/1.50  tff(c_164, plain, (![A_76, C_77]: (r2_hidden(A_76, C_77) | ~r1_tarski(k1_tarski(A_76), C_77))), inference(superposition, [status(thm), theory('equality')], [c_14, c_131])).
% 3.06/1.50  tff(c_176, plain, (![A_32]: (r2_hidden(A_32, k1_zfmisc_1(A_32)))), inference(resolution, [status(thm)], [c_74, c_164])).
% 3.06/1.50  tff(c_26, plain, (![A_29, B_30]: (r1_xboole_0(k1_tarski(A_29), B_30) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.50  tff(c_270, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, B_95) | ~r2_hidden(C_96, A_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.50  tff(c_516, plain, (![C_155, B_156, A_157]: (~r2_hidden(C_155, B_156) | ~r2_hidden(C_155, k1_tarski(A_157)) | r2_hidden(A_157, B_156))), inference(resolution, [status(thm)], [c_26, c_270])).
% 3.06/1.50  tff(c_625, plain, (![A_167, A_168]: (~r2_hidden(A_167, k1_tarski(A_168)) | r2_hidden(A_168, k1_zfmisc_1(A_167)))), inference(resolution, [status(thm)], [c_176, c_516])).
% 3.06/1.50  tff(c_639, plain, (r2_hidden('#skF_3', k1_zfmisc_1(k1_mcart_1('#skF_2')))), inference(resolution, [status(thm)], [c_328, c_625])).
% 3.06/1.50  tff(c_38, plain, (![A_36, B_37]: (m1_subset_1(A_36, B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.50  tff(c_650, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_mcart_1('#skF_2')))), inference(resolution, [status(thm)], [c_639, c_38])).
% 3.06/1.50  tff(c_40, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.06/1.50  tff(c_661, plain, (r1_tarski('#skF_3', k1_mcart_1('#skF_2'))), inference(resolution, [status(thm)], [c_650, c_40])).
% 3.06/1.50  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.50  tff(c_672, plain, (k1_mcart_1('#skF_2')='#skF_3' | ~r1_tarski(k1_mcart_1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_661, c_8])).
% 3.06/1.50  tff(c_675, plain, (~r1_tarski(k1_mcart_1('#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_81, c_672])).
% 3.06/1.50  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.50  tff(c_103, plain, (![B_60, C_61, A_62]: (r2_hidden(B_60, C_61) | ~r1_tarski(k2_tarski(A_62, B_60), C_61))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.06/1.50  tff(c_117, plain, (![B_63, A_64]: (r2_hidden(B_63, k2_tarski(A_64, B_63)))), inference(resolution, [status(thm)], [c_12, c_103])).
% 3.06/1.50  tff(c_123, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_117])).
% 3.06/1.50  tff(c_584, plain, (![A_164, A_165]: (~r2_hidden(A_164, k1_tarski(A_165)) | r2_hidden(A_165, k1_tarski(A_164)))), inference(resolution, [status(thm)], [c_123, c_516])).
% 3.06/1.50  tff(c_595, plain, (r2_hidden('#skF_3', k1_tarski(k1_mcart_1('#skF_2')))), inference(resolution, [status(thm)], [c_328, c_584])).
% 3.06/1.50  tff(c_638, plain, (r2_hidden(k1_mcart_1('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_595, c_625])).
% 3.06/1.50  tff(c_657, plain, (m1_subset_1(k1_mcart_1('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_638, c_38])).
% 3.06/1.50  tff(c_678, plain, (r1_tarski(k1_mcart_1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_657, c_40])).
% 3.06/1.50  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_675, c_678])).
% 3.06/1.50  tff(c_683, plain, (~r2_hidden(k2_mcart_1('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.06/1.50  tff(c_881, plain, (![A_220, C_221, B_222]: (r2_hidden(k2_mcart_1(A_220), C_221) | ~r2_hidden(A_220, k2_zfmisc_1(B_222, C_221)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.50  tff(c_889, plain, (r2_hidden(k2_mcart_1('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_881])).
% 3.06/1.50  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_683, c_889])).
% 3.06/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.50  
% 3.06/1.50  Inference rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Ref     : 0
% 3.06/1.50  #Sup     : 188
% 3.06/1.50  #Fact    : 0
% 3.06/1.50  #Define  : 0
% 3.06/1.50  #Split   : 1
% 3.06/1.50  #Chain   : 0
% 3.06/1.50  #Close   : 0
% 3.06/1.50  
% 3.06/1.50  Ordering : KBO
% 3.06/1.50  
% 3.06/1.50  Simplification rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Subsume      : 3
% 3.06/1.50  #Demod        : 76
% 3.06/1.50  #Tautology    : 73
% 3.06/1.50  #SimpNegUnit  : 3
% 3.06/1.50  #BackRed      : 0
% 3.06/1.50  
% 3.06/1.50  #Partial instantiations: 0
% 3.06/1.50  #Strategies tried      : 1
% 3.06/1.50  
% 3.06/1.50  Timing (in seconds)
% 3.06/1.50  ----------------------
% 3.06/1.50  Preprocessing        : 0.33
% 3.06/1.50  Parsing              : 0.18
% 3.06/1.50  CNF conversion       : 0.02
% 3.06/1.50  Main loop            : 0.39
% 3.06/1.50  Inferencing          : 0.15
% 3.06/1.50  Reduction            : 0.12
% 3.06/1.50  Demodulation         : 0.09
% 3.06/1.51  BG Simplification    : 0.02
% 3.06/1.51  Subsumption          : 0.06
% 3.06/1.51  Abstraction          : 0.02
% 3.06/1.51  MUC search           : 0.00
% 3.06/1.51  Cooper               : 0.00
% 3.06/1.51  Total                : 0.75
% 3.06/1.51  Index Insertion      : 0.00
% 3.06/1.51  Index Deletion       : 0.00
% 3.06/1.51  Index Matching       : 0.00
% 3.06/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
