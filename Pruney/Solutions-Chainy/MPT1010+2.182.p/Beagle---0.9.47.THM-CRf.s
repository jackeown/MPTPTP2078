%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
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
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

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
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_27,B_28] : k2_xboole_0(k1_tarski(A_27),B_28) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_27] : k1_tarski(A_27) != k1_xboole_0 ),
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
    ! [D_109,C_110,B_111,A_112] :
      ( r2_hidden(k1_funct_1(D_109,C_110),B_111)
      | k1_xboole_0 = B_111
      | ~ r2_hidden(C_110,A_112)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(D_109,A_112,B_111)
      | ~ v1_funct_1(D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_271,plain,(
    ! [D_113,B_114] :
      ( r2_hidden(k1_funct_1(D_113,'#skF_5'),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_114)))
      | ~ v1_funct_2(D_113,'#skF_3',B_114)
      | ~ v1_funct_1(D_113) ) ),
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
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [F_63,A_66,D_62,C_64,B_65] :
      ( F_63 = D_62
      | F_63 = C_64
      | F_63 = B_65
      | F_63 = A_66
      | ~ r2_hidden(F_63,k2_enumset1(A_66,B_65,C_64,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_170,plain,(
    ! [F_75,C_76,B_77,A_78] :
      ( F_75 = C_76
      | F_75 = B_77
      | F_75 = A_78
      | F_75 = A_78
      | ~ r2_hidden(F_75,k1_enumset1(A_78,B_77,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_190,plain,(
    ! [F_84,B_85,A_86] :
      ( F_84 = B_85
      | F_84 = A_86
      | F_84 = A_86
      | F_84 = A_86
      | ~ r2_hidden(F_84,k2_tarski(A_86,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_199,plain,(
    ! [F_84,A_2] :
      ( F_84 = A_2
      | F_84 = A_2
      | F_84 = A_2
      | F_84 = A_2
      | ~ r2_hidden(F_84,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_190])).

tff(c_283,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_278,c_199])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_46,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.10/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.10/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.30  
% 2.10/1.31  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.10/1.31  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.10/1.31  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.10/1.31  tff(f_68, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.10/1.31  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.10/1.31  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.10/1.31  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.10/1.31  tff(f_56, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.10/1.31  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.31  tff(c_64, plain, (![A_27, B_28]: (k2_xboole_0(k1_tarski(A_27), B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.31  tff(c_68, plain, (![A_27]: (k1_tarski(A_27)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 2.10/1.31  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_234, plain, (![D_109, C_110, B_111, A_112]: (r2_hidden(k1_funct_1(D_109, C_110), B_111) | k1_xboole_0=B_111 | ~r2_hidden(C_110, A_112) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(D_109, A_112, B_111) | ~v1_funct_1(D_109))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.31  tff(c_271, plain, (![D_113, B_114]: (r2_hidden(k1_funct_1(D_113, '#skF_5'), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_114))) | ~v1_funct_2(D_113, '#skF_3', B_114) | ~v1_funct_1(D_113))), inference(resolution, [status(thm)], [c_48, c_234])).
% 2.10/1.31  tff(c_274, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_271])).
% 2.10/1.31  tff(c_277, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_274])).
% 2.10/1.31  tff(c_278, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_277])).
% 2.10/1.31  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.31  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.31  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.31  tff(c_131, plain, (![F_63, A_66, D_62, C_64, B_65]: (F_63=D_62 | F_63=C_64 | F_63=B_65 | F_63=A_66 | ~r2_hidden(F_63, k2_enumset1(A_66, B_65, C_64, D_62)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.31  tff(c_170, plain, (![F_75, C_76, B_77, A_78]: (F_75=C_76 | F_75=B_77 | F_75=A_78 | F_75=A_78 | ~r2_hidden(F_75, k1_enumset1(A_78, B_77, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_131])).
% 2.10/1.31  tff(c_190, plain, (![F_84, B_85, A_86]: (F_84=B_85 | F_84=A_86 | F_84=A_86 | F_84=A_86 | ~r2_hidden(F_84, k2_tarski(A_86, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_170])).
% 2.10/1.31  tff(c_199, plain, (![F_84, A_2]: (F_84=A_2 | F_84=A_2 | F_84=A_2 | F_84=A_2 | ~r2_hidden(F_84, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_190])).
% 2.10/1.31  tff(c_283, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_278, c_199])).
% 2.10/1.31  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_46, c_283])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 52
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 0
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 0
% 2.10/1.31  #Demod        : 5
% 2.10/1.31  #Tautology    : 23
% 2.10/1.31  #SimpNegUnit  : 2
% 2.10/1.31  #BackRed      : 0
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.32  Preprocessing        : 0.31
% 2.10/1.32  Parsing              : 0.15
% 2.10/1.32  CNF conversion       : 0.02
% 2.10/1.32  Main loop            : 0.23
% 2.10/1.32  Inferencing          : 0.08
% 2.10/1.32  Reduction            : 0.07
% 2.10/1.32  Demodulation         : 0.05
% 2.10/1.32  BG Simplification    : 0.02
% 2.10/1.32  Subsumption          : 0.06
% 2.10/1.32  Abstraction          : 0.02
% 2.10/1.32  MUC search           : 0.00
% 2.10/1.32  Cooper               : 0.00
% 2.10/1.32  Total                : 0.57
% 2.10/1.32  Index Insertion      : 0.00
% 2.10/1.32  Index Deletion       : 0.00
% 2.10/1.32  Index Matching       : 0.00
% 2.10/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
