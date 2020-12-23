%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 114 expanded)
%              Number of equality atoms :   41 (  53 expanded)
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

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

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

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k1_tarski(B_49)) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_50,B_51] : k2_tarski(A_50,B_51) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_12])).

tff(c_91,plain,(
    ! [A_3] : k1_tarski(A_3) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_89])).

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

tff(c_214,plain,(
    ! [D_108,C_109,B_110,A_111] :
      ( r2_hidden(k1_funct_1(D_108,C_109),B_110)
      | k1_xboole_0 = B_110
      | ~ r2_hidden(C_109,A_111)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_2(D_108,A_111,B_110)
      | ~ v1_funct_1(D_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_248,plain,(
    ! [D_112,B_113] :
      ( r2_hidden(k1_funct_1(D_112,'#skF_5'),B_113)
      | k1_xboole_0 = B_113
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2(D_112,'#skF_3',B_113)
      | ~ v1_funct_1(D_112) ) ),
    inference(resolution,[status(thm)],[c_48,c_214])).

tff(c_251,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_248])).

tff(c_254,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_251])).

tff(c_255,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_254])).

tff(c_6,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [C_74,A_78,D_75,F_77,B_76] :
      ( F_77 = D_75
      | F_77 = C_74
      | F_77 = B_76
      | F_77 = A_78
      | ~ r2_hidden(F_77,k2_enumset1(A_78,B_76,C_74,D_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_172,plain,(
    ! [F_84,C_85,B_86,A_87] :
      ( F_84 = C_85
      | F_84 = B_86
      | F_84 = A_87
      | F_84 = A_87
      | ~ r2_hidden(F_84,k1_enumset1(A_87,B_86,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_147])).

tff(c_191,plain,(
    ! [F_88,B_89,A_90] :
      ( F_88 = B_89
      | F_88 = A_90
      | F_88 = A_90
      | F_88 = A_90
      | ~ r2_hidden(F_88,k2_tarski(A_90,B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_172])).

tff(c_200,plain,(
    ! [F_88,A_3] :
      ( F_88 = A_3
      | F_88 = A_3
      | F_88 = A_3
      | F_88 = A_3
      | ~ r2_hidden(F_88,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_191])).

tff(c_260,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_255,c_200])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_46,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:55:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.30  
% 2.18/1.30  %Foreground sorts:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Background operators:
% 2.18/1.30  
% 2.18/1.30  
% 2.18/1.30  %Foreground operators:
% 2.18/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.30  
% 2.18/1.31  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.18/1.31  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.31  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.18/1.31  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.18/1.31  tff(f_68, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.18/1.31  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.18/1.31  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.18/1.31  tff(f_56, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.18/1.31  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.31  tff(c_78, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(B_49))=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.31  tff(c_12, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.18/1.31  tff(c_89, plain, (![A_50, B_51]: (k2_tarski(A_50, B_51)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_12])).
% 2.18/1.31  tff(c_91, plain, (![A_3]: (k1_tarski(A_3)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_89])).
% 2.18/1.31  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_214, plain, (![D_108, C_109, B_110, A_111]: (r2_hidden(k1_funct_1(D_108, C_109), B_110) | k1_xboole_0=B_110 | ~r2_hidden(C_109, A_111) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_2(D_108, A_111, B_110) | ~v1_funct_1(D_108))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.31  tff(c_248, plain, (![D_112, B_113]: (r2_hidden(k1_funct_1(D_112, '#skF_5'), B_113) | k1_xboole_0=B_113 | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2(D_112, '#skF_3', B_113) | ~v1_funct_1(D_112))), inference(resolution, [status(thm)], [c_48, c_214])).
% 2.18/1.31  tff(c_251, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_248])).
% 2.18/1.31  tff(c_254, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_251])).
% 2.18/1.31  tff(c_255, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_254])).
% 2.18/1.31  tff(c_6, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.31  tff(c_8, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.31  tff(c_147, plain, (![C_74, A_78, D_75, F_77, B_76]: (F_77=D_75 | F_77=C_74 | F_77=B_76 | F_77=A_78 | ~r2_hidden(F_77, k2_enumset1(A_78, B_76, C_74, D_75)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.31  tff(c_172, plain, (![F_84, C_85, B_86, A_87]: (F_84=C_85 | F_84=B_86 | F_84=A_87 | F_84=A_87 | ~r2_hidden(F_84, k1_enumset1(A_87, B_86, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_147])).
% 2.18/1.31  tff(c_191, plain, (![F_88, B_89, A_90]: (F_88=B_89 | F_88=A_90 | F_88=A_90 | F_88=A_90 | ~r2_hidden(F_88, k2_tarski(A_90, B_89)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_172])).
% 2.18/1.31  tff(c_200, plain, (![F_88, A_3]: (F_88=A_3 | F_88=A_3 | F_88=A_3 | F_88=A_3 | ~r2_hidden(F_88, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_191])).
% 2.18/1.31  tff(c_260, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_255, c_200])).
% 2.18/1.31  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_46, c_260])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 48
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 0
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 0
% 2.18/1.31  #Demod        : 5
% 2.18/1.31  #Tautology    : 23
% 2.18/1.31  #SimpNegUnit  : 2
% 2.18/1.31  #BackRed      : 0
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.31  Preprocessing        : 0.33
% 2.18/1.31  Parsing              : 0.17
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.21
% 2.18/1.31  Inferencing          : 0.08
% 2.18/1.31  Reduction            : 0.06
% 2.18/1.31  Demodulation         : 0.05
% 2.18/1.31  BG Simplification    : 0.02
% 2.18/1.31  Subsumption          : 0.05
% 2.18/1.31  Abstraction          : 0.02
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.57
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
