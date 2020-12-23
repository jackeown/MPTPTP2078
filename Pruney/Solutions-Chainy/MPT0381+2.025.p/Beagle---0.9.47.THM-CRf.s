%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 101 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(A_64,B_65) = A_64
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_103,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_135,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_135])).

tff(c_147,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_144])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    ! [B_53,A_54] :
      ( ~ r2_hidden(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_168,plain,(
    ! [B_78,A_79] :
      ( m1_subset_1(B_78,A_79)
      | ~ r2_hidden(B_78,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_177,plain,
    ( m1_subset_1('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_182,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_177])).

tff(c_206,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(k1_tarski(B_86),k1_zfmisc_1(A_87))
      | k1_xboole_0 = A_87
      | ~ m1_subset_1(B_86,A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_212,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_46])).

tff(c_216,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_212])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r1_xboole_0(A_71,B_72)
      | ~ r2_hidden(C_73,k3_xboole_0(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [A_14,C_73] :
      ( ~ r1_xboole_0(k1_xboole_0,A_14)
      | ~ r2_hidden(C_73,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_121])).

tff(c_156,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_166,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_156])).

tff(c_218,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_166])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_218])).

tff(c_227,plain,(
    ! [A_88] : ~ r1_xboole_0(k1_xboole_0,A_88) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_231,plain,(
    ! [B_17] : k4_xboole_0(k1_xboole_0,B_17) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_227])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.15/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.25  
% 2.15/1.26  tff(f_55, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.15/1.26  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.26  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.15/1.26  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.15/1.26  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.15/1.26  tff(f_98, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.15/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.15/1.26  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.15/1.26  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.15/1.26  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.15/1.26  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.26  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.26  tff(c_99, plain, (![A_64, B_65]: (k3_xboole_0(A_64, B_65)=A_64 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.26  tff(c_103, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_99])).
% 2.15/1.26  tff(c_135, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.15/1.26  tff(c_144, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_103, c_135])).
% 2.15/1.26  tff(c_147, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_144])).
% 2.15/1.26  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.26  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.15/1.26  tff(c_68, plain, (![B_53, A_54]: (~r2_hidden(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.26  tff(c_72, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_68])).
% 2.15/1.26  tff(c_168, plain, (![B_78, A_79]: (m1_subset_1(B_78, A_79) | ~r2_hidden(B_78, A_79) | v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.15/1.26  tff(c_177, plain, (m1_subset_1('#skF_3', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_168])).
% 2.15/1.26  tff(c_182, plain, (m1_subset_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_177])).
% 2.15/1.26  tff(c_206, plain, (![B_86, A_87]: (m1_subset_1(k1_tarski(B_86), k1_zfmisc_1(A_87)) | k1_xboole_0=A_87 | ~m1_subset_1(B_86, A_87))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.15/1.26  tff(c_46, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.15/1.26  tff(c_212, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_206, c_46])).
% 2.15/1.26  tff(c_216, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_212])).
% 2.15/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.26  tff(c_121, plain, (![A_71, B_72, C_73]: (~r1_xboole_0(A_71, B_72) | ~r2_hidden(C_73, k3_xboole_0(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.26  tff(c_128, plain, (![A_14, C_73]: (~r1_xboole_0(k1_xboole_0, A_14) | ~r2_hidden(C_73, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_121])).
% 2.15/1.26  tff(c_156, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_128])).
% 2.15/1.26  tff(c_166, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_156])).
% 2.15/1.26  tff(c_218, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_166])).
% 2.15/1.26  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_218])).
% 2.15/1.26  tff(c_227, plain, (![A_88]: (~r1_xboole_0(k1_xboole_0, A_88))), inference(splitRight, [status(thm)], [c_128])).
% 2.15/1.26  tff(c_231, plain, (![B_17]: (k4_xboole_0(k1_xboole_0, B_17)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_227])).
% 2.15/1.26  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_147, c_231])).
% 2.15/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  Inference rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Ref     : 0
% 2.15/1.26  #Sup     : 36
% 2.15/1.26  #Fact    : 0
% 2.15/1.26  #Define  : 0
% 2.15/1.26  #Split   : 2
% 2.15/1.26  #Chain   : 0
% 2.15/1.26  #Close   : 0
% 2.15/1.26  
% 2.15/1.26  Ordering : KBO
% 2.15/1.26  
% 2.15/1.26  Simplification rules
% 2.15/1.26  ----------------------
% 2.15/1.26  #Subsume      : 1
% 2.15/1.26  #Demod        : 14
% 2.15/1.26  #Tautology    : 22
% 2.15/1.26  #SimpNegUnit  : 2
% 2.15/1.26  #BackRed      : 7
% 2.15/1.26  
% 2.15/1.26  #Partial instantiations: 0
% 2.15/1.26  #Strategies tried      : 1
% 2.15/1.26  
% 2.15/1.26  Timing (in seconds)
% 2.15/1.26  ----------------------
% 2.15/1.26  Preprocessing        : 0.32
% 2.15/1.26  Parsing              : 0.17
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.17
% 2.15/1.26  Inferencing          : 0.06
% 2.15/1.26  Reduction            : 0.05
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.01
% 2.15/1.26  Subsumption          : 0.03
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.52
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
