%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   60 (  89 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 179 expanded)
%              Number of equality atoms :   37 (  66 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_270,plain,(
    ! [D_125,C_126,B_127,A_128] :
      ( r2_hidden(k1_funct_1(D_125,C_126),B_127)
      | k1_xboole_0 = B_127
      | ~ r2_hidden(C_126,A_128)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127)))
      | ~ v1_funct_2(D_125,A_128,B_127)
      | ~ v1_funct_1(D_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_304,plain,(
    ! [D_129,B_130] :
      ( r2_hidden(k1_funct_1(D_129,'#skF_5'),B_130)
      | k1_xboole_0 = B_130
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_130)))
      | ~ v1_funct_2(D_129,'#skF_3',B_130)
      | ~ v1_funct_1(D_129) ) ),
    inference(resolution,[status(thm)],[c_46,c_270])).

tff(c_307,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_304])).

tff(c_310,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_307])).

tff(c_311,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_48,B_49,C_50] : k2_enumset1(A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [F_15,A_8,B_9,C_10] : r2_hidden(F_15,k2_enumset1(A_8,B_9,C_10,F_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [C_51,A_52,B_53] : r2_hidden(C_51,k1_enumset1(A_52,B_53,C_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_130,plain,(
    ! [B_54,A_55] : r2_hidden(B_54,k2_tarski(A_55,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_122])).

tff(c_138,plain,(
    ! [A_56] : r2_hidden(A_56,k1_tarski(A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_130])).

tff(c_40,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    ! [A_56] : ~ r1_tarski(k1_tarski(A_56),A_56) ),
    inference(resolution,[status(thm)],[c_138,c_40])).

tff(c_320,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_142])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_329,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_57,D_61,B_58,F_60,C_59] :
      ( F_60 = D_61
      | F_60 = C_59
      | F_60 = B_58
      | F_60 = A_57
      | ~ r2_hidden(F_60,k2_enumset1(A_57,B_58,C_59,D_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_230,plain,(
    ! [F_111,C_112,B_113,A_114] :
      ( F_111 = C_112
      | F_111 = B_113
      | F_111 = A_114
      | F_111 = A_114
      | ~ r2_hidden(F_111,k1_enumset1(A_114,B_113,C_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_143])).

tff(c_249,plain,(
    ! [F_115,B_116,A_117] :
      ( F_115 = B_116
      | F_115 = A_117
      | F_115 = A_117
      | F_115 = A_117
      | ~ r2_hidden(F_115,k2_tarski(A_117,B_116)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_258,plain,(
    ! [F_115,A_2] :
      ( F_115 = A_2
      | F_115 = A_2
      | F_115 = A_2
      | F_115 = A_2
      | ~ r2_hidden(F_115,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_249])).

tff(c_363,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_329,c_258])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_44,c_44,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  
% 2.47/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.37  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.47/1.37  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.47/1.37  tff(f_68, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.47/1.37  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.47/1.37  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.47/1.37  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.47/1.37  tff(f_51, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.47/1.37  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.47/1.37  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.37  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.37  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.37  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.37  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.37  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.37  tff(c_270, plain, (![D_125, C_126, B_127, A_128]: (r2_hidden(k1_funct_1(D_125, C_126), B_127) | k1_xboole_0=B_127 | ~r2_hidden(C_126, A_128) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))) | ~v1_funct_2(D_125, A_128, B_127) | ~v1_funct_1(D_125))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.47/1.37  tff(c_304, plain, (![D_129, B_130]: (r2_hidden(k1_funct_1(D_129, '#skF_5'), B_130) | k1_xboole_0=B_130 | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_130))) | ~v1_funct_2(D_129, '#skF_3', B_130) | ~v1_funct_1(D_129))), inference(resolution, [status(thm)], [c_46, c_270])).
% 2.47/1.37  tff(c_307, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_304])).
% 2.47/1.37  tff(c_310, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_307])).
% 2.47/1.37  tff(c_311, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_310])).
% 2.47/1.37  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.37  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.37  tff(c_98, plain, (![A_48, B_49, C_50]: (k2_enumset1(A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.37  tff(c_12, plain, (![F_15, A_8, B_9, C_10]: (r2_hidden(F_15, k2_enumset1(A_8, B_9, C_10, F_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.37  tff(c_122, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, k1_enumset1(A_52, B_53, C_51)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 2.47/1.37  tff(c_130, plain, (![B_54, A_55]: (r2_hidden(B_54, k2_tarski(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_122])).
% 2.47/1.37  tff(c_138, plain, (![A_56]: (r2_hidden(A_56, k1_tarski(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_130])).
% 2.47/1.37  tff(c_40, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.47/1.37  tff(c_142, plain, (![A_56]: (~r1_tarski(k1_tarski(A_56), A_56))), inference(resolution, [status(thm)], [c_138, c_40])).
% 2.47/1.37  tff(c_320, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_311, c_142])).
% 2.47/1.37  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_320])).
% 2.47/1.37  tff(c_329, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_310])).
% 2.47/1.37  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.47/1.37  tff(c_143, plain, (![A_57, D_61, B_58, F_60, C_59]: (F_60=D_61 | F_60=C_59 | F_60=B_58 | F_60=A_57 | ~r2_hidden(F_60, k2_enumset1(A_57, B_58, C_59, D_61)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.37  tff(c_230, plain, (![F_111, C_112, B_113, A_114]: (F_111=C_112 | F_111=B_113 | F_111=A_114 | F_111=A_114 | ~r2_hidden(F_111, k1_enumset1(A_114, B_113, C_112)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_143])).
% 2.47/1.37  tff(c_249, plain, (![F_115, B_116, A_117]: (F_115=B_116 | F_115=A_117 | F_115=A_117 | F_115=A_117 | ~r2_hidden(F_115, k2_tarski(A_117, B_116)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_230])).
% 2.47/1.37  tff(c_258, plain, (![F_115, A_2]: (F_115=A_2 | F_115=A_2 | F_115=A_2 | F_115=A_2 | ~r2_hidden(F_115, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_249])).
% 2.47/1.37  tff(c_363, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_329, c_258])).
% 2.47/1.37  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_44, c_44, c_363])).
% 2.47/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  Inference rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Ref     : 0
% 2.47/1.37  #Sup     : 74
% 2.47/1.37  #Fact    : 0
% 2.47/1.37  #Define  : 0
% 2.47/1.37  #Split   : 1
% 2.47/1.37  #Chain   : 0
% 2.47/1.37  #Close   : 0
% 2.47/1.37  
% 2.47/1.37  Ordering : KBO
% 2.47/1.37  
% 2.47/1.37  Simplification rules
% 2.47/1.37  ----------------------
% 2.47/1.37  #Subsume      : 9
% 2.47/1.37  #Demod        : 8
% 2.47/1.37  #Tautology    : 20
% 2.47/1.37  #SimpNegUnit  : 1
% 2.47/1.37  #BackRed      : 2
% 2.47/1.37  
% 2.47/1.37  #Partial instantiations: 0
% 2.47/1.37  #Strategies tried      : 1
% 2.47/1.37  
% 2.47/1.37  Timing (in seconds)
% 2.47/1.37  ----------------------
% 2.62/1.37  Preprocessing        : 0.32
% 2.62/1.37  Parsing              : 0.17
% 2.62/1.37  CNF conversion       : 0.02
% 2.62/1.37  Main loop            : 0.26
% 2.62/1.37  Inferencing          : 0.09
% 2.62/1.37  Reduction            : 0.07
% 2.62/1.37  Demodulation         : 0.05
% 2.62/1.37  BG Simplification    : 0.02
% 2.62/1.37  Subsumption          : 0.07
% 2.62/1.37  Abstraction          : 0.02
% 2.62/1.37  MUC search           : 0.00
% 2.62/1.37  Cooper               : 0.00
% 2.62/1.37  Total                : 0.61
% 2.62/1.37  Index Insertion      : 0.00
% 2.62/1.37  Index Deletion       : 0.00
% 2.62/1.37  Index Matching       : 0.00
% 2.62/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
