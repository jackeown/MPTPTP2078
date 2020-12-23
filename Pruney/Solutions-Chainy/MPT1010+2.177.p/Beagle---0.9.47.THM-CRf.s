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
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   53 (  63 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 111 expanded)
%              Number of equality atoms :   40 (  50 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),B_29) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_28] : k1_tarski(A_28) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_234,plain,(
    ! [D_110,C_111,B_112,A_113] :
      ( r2_hidden(k1_funct_1(D_110,C_111),B_112)
      | k1_xboole_0 = B_112
      | ~ r2_hidden(C_111,A_113)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112)))
      | ~ v1_funct_2(D_110,A_113,B_112)
      | ~ v1_funct_1(D_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_271,plain,(
    ! [D_114,B_115] :
      ( r2_hidden(k1_funct_1(D_114,'#skF_5'),B_115)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(D_114,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_115)))
      | ~ v1_funct_2(D_114,'#skF_3',B_115)
      | ~ v1_funct_1(D_114) ) ),
    inference(resolution,[status(thm)],[c_48,c_234])).

tff(c_274,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_277,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_274])).

tff(c_278,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_277])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [C_63,D_64,A_67,F_66,B_65] :
      ( F_66 = D_64
      | F_66 = C_63
      | F_66 = B_65
      | F_66 = A_67
      | ~ r2_hidden(F_66,k2_enumset1(A_67,B_65,C_63,D_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [F_76,C_77,B_78,A_79] :
      ( F_76 = C_77
      | F_76 = B_78
      | F_76 = A_79
      | F_76 = A_79
      | ~ r2_hidden(F_76,k1_enumset1(A_79,B_78,C_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_190,plain,(
    ! [F_85,B_86,A_87] :
      ( F_85 = B_86
      | F_85 = A_87
      | F_85 = A_87
      | F_85 = A_87
      | ~ r2_hidden(F_85,k2_tarski(A_87,B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_199,plain,(
    ! [F_85,A_3] :
      ( F_85 = A_3
      | F_85 = A_3
      | F_85 = A_3
      | F_85 = A_3
      | ~ r2_hidden(F_85,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_283,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_278,c_199])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_46,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.33  
% 2.13/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.33  
% 2.49/1.33  %Foreground sorts:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Background operators:
% 2.49/1.33  
% 2.49/1.33  
% 2.49/1.33  %Foreground operators:
% 2.49/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.49/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.49/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.33  
% 2.49/1.35  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.49/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.49/1.35  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.49/1.35  tff(f_68, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.49/1.35  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.49/1.35  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.49/1.35  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.49/1.35  tff(f_56, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.49/1.35  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.35  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.35  tff(c_64, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.35  tff(c_68, plain, (![A_28]: (k1_tarski(A_28)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.49/1.35  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.35  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.35  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.35  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.49/1.35  tff(c_234, plain, (![D_110, C_111, B_112, A_113]: (r2_hidden(k1_funct_1(D_110, C_111), B_112) | k1_xboole_0=B_112 | ~r2_hidden(C_111, A_113) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))) | ~v1_funct_2(D_110, A_113, B_112) | ~v1_funct_1(D_110))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.49/1.35  tff(c_271, plain, (![D_114, B_115]: (r2_hidden(k1_funct_1(D_114, '#skF_5'), B_115) | k1_xboole_0=B_115 | ~m1_subset_1(D_114, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_115))) | ~v1_funct_2(D_114, '#skF_3', B_115) | ~v1_funct_1(D_114))), inference(resolution, [status(thm)], [c_48, c_234])).
% 2.49/1.35  tff(c_274, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_271])).
% 2.49/1.35  tff(c_277, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_274])).
% 2.49/1.35  tff(c_278, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_277])).
% 2.49/1.35  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.35  tff(c_6, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.35  tff(c_8, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.35  tff(c_131, plain, (![C_63, D_64, A_67, F_66, B_65]: (F_66=D_64 | F_66=C_63 | F_66=B_65 | F_66=A_67 | ~r2_hidden(F_66, k2_enumset1(A_67, B_65, C_63, D_64)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.35  tff(c_170, plain, (![F_76, C_77, B_78, A_79]: (F_76=C_77 | F_76=B_78 | F_76=A_79 | F_76=A_79 | ~r2_hidden(F_76, k1_enumset1(A_79, B_78, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_131])).
% 2.49/1.35  tff(c_190, plain, (![F_85, B_86, A_87]: (F_85=B_86 | F_85=A_87 | F_85=A_87 | F_85=A_87 | ~r2_hidden(F_85, k2_tarski(A_87, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_170])).
% 2.49/1.35  tff(c_199, plain, (![F_85, A_3]: (F_85=A_3 | F_85=A_3 | F_85=A_3 | F_85=A_3 | ~r2_hidden(F_85, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_190])).
% 2.49/1.35  tff(c_283, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_278, c_199])).
% 2.49/1.35  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_46, c_283])).
% 2.49/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.35  
% 2.49/1.35  Inference rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Ref     : 0
% 2.49/1.35  #Sup     : 52
% 2.49/1.35  #Fact    : 0
% 2.49/1.35  #Define  : 0
% 2.49/1.35  #Split   : 0
% 2.49/1.35  #Chain   : 0
% 2.49/1.35  #Close   : 0
% 2.49/1.35  
% 2.49/1.35  Ordering : KBO
% 2.49/1.35  
% 2.49/1.35  Simplification rules
% 2.49/1.35  ----------------------
% 2.49/1.35  #Subsume      : 0
% 2.49/1.35  #Demod        : 5
% 2.49/1.35  #Tautology    : 23
% 2.49/1.35  #SimpNegUnit  : 2
% 2.49/1.35  #BackRed      : 0
% 2.49/1.35  
% 2.49/1.35  #Partial instantiations: 0
% 2.49/1.35  #Strategies tried      : 1
% 2.49/1.35  
% 2.49/1.35  Timing (in seconds)
% 2.49/1.35  ----------------------
% 2.49/1.35  Preprocessing        : 0.33
% 2.49/1.35  Parsing              : 0.16
% 2.49/1.35  CNF conversion       : 0.02
% 2.49/1.35  Main loop            : 0.25
% 2.49/1.35  Inferencing          : 0.09
% 2.49/1.35  Reduction            : 0.07
% 2.49/1.35  Demodulation         : 0.05
% 2.49/1.35  BG Simplification    : 0.02
% 2.49/1.35  Subsumption          : 0.06
% 2.49/1.35  Abstraction          : 0.02
% 2.49/1.35  MUC search           : 0.00
% 2.49/1.35  Cooper               : 0.00
% 2.49/1.35  Total                : 0.61
% 2.49/1.35  Index Insertion      : 0.00
% 2.49/1.35  Index Deletion       : 0.00
% 2.49/1.35  Index Matching       : 0.00
% 2.49/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
