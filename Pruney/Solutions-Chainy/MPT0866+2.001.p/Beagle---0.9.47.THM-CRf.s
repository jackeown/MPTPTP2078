%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:20 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 111 expanded)
%              Number of equality atoms :   37 (  60 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_10 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(k1_tarski(B_9),k1_zfmisc_1(A_8))
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(B_9,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_370,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k4_tarski('#skF_6'(A_108,B_109,C_110,D_111),'#skF_7'(A_108,B_109,C_110,D_111)) = A_108
      | ~ r2_hidden(A_108,D_111)
      | ~ m1_subset_1(D_111,k1_zfmisc_1(k2_zfmisc_1(B_109,C_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_677,plain,(
    ! [A_193,B_194,C_195,B_196] :
      ( k4_tarski('#skF_6'(A_193,B_194,C_195,k1_tarski(B_196)),'#skF_7'(A_193,B_194,C_195,k1_tarski(B_196))) = A_193
      | ~ r2_hidden(A_193,k1_tarski(B_196))
      | k2_zfmisc_1(B_194,C_195) = k1_xboole_0
      | ~ m1_subset_1(B_196,k2_zfmisc_1(B_194,C_195)) ) ),
    inference(resolution,[status(thm)],[c_20,c_370])).

tff(c_93,plain,(
    ! [A_53,B_54] :
      ( k4_tarski(k1_mcart_1(A_53),k2_mcart_1(A_53)) = A_53
      | ~ r2_hidden(A_53,B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_109,plain,(
    ! [C_57] :
      ( k4_tarski(k1_mcart_1(C_57),k2_mcart_1(C_57)) = C_57
      | ~ v1_relat_1(k1_tarski(C_57)) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_36,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_121,plain,(
    ~ v1_relat_1(k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_36])).

tff(c_72,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_3'(A_42),A_42)
      | v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_1] :
      ( '#skF_3'(k1_tarski(A_1)) = A_1
      | v1_relat_1(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_126,plain,(
    '#skF_3'(k1_tarski('#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_77,c_121])).

tff(c_24,plain,(
    ! [C_23,D_24,A_10] :
      ( k4_tarski(C_23,D_24) != '#skF_3'(A_10)
      | v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_129,plain,(
    ! [C_23,D_24] :
      ( k4_tarski(C_23,D_24) != '#skF_10'
      | v1_relat_1(k1_tarski('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_24])).

tff(c_135,plain,(
    ! [C_23,D_24] : k4_tarski(C_23,D_24) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_129])).

tff(c_716,plain,(
    ! [A_197,B_198,B_199,C_200] :
      ( A_197 != '#skF_10'
      | ~ r2_hidden(A_197,k1_tarski(B_198))
      | k2_zfmisc_1(B_199,C_200) = k1_xboole_0
      | ~ m1_subset_1(B_198,k2_zfmisc_1(B_199,C_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_135])).

tff(c_749,plain,(
    ! [C_201,B_202,C_203] :
      ( C_201 != '#skF_10'
      | k2_zfmisc_1(B_202,C_203) = k1_xboole_0
      | ~ m1_subset_1(C_201,k2_zfmisc_1(B_202,C_203)) ) ),
    inference(resolution,[status(thm)],[c_4,c_716])).

tff(c_759,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_749])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_775,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_14])).

tff(c_782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  
% 2.69/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_10 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.69/1.44  
% 2.69/1.44  %Foreground sorts:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Background operators:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Foreground operators:
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.44  tff('#skF_10', type, '#skF_10': $i).
% 2.69/1.44  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 2.69/1.44  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.69/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.69/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.44  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.69/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.44  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.45  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.69/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.69/1.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.69/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.45  
% 2.69/1.46  tff(f_88, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.69/1.46  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.69/1.46  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.69/1.46  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.69/1.46  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.69/1.46  tff(f_55, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.69/1.46  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.69/1.46  tff(c_42, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.69/1.46  tff(c_40, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.69/1.46  tff(c_38, plain, (m1_subset_1('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.69/1.46  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.46  tff(c_20, plain, (![B_9, A_8]: (m1_subset_1(k1_tarski(B_9), k1_zfmisc_1(A_8)) | k1_xboole_0=A_8 | ~m1_subset_1(B_9, A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.46  tff(c_370, plain, (![A_108, B_109, C_110, D_111]: (k4_tarski('#skF_6'(A_108, B_109, C_110, D_111), '#skF_7'(A_108, B_109, C_110, D_111))=A_108 | ~r2_hidden(A_108, D_111) | ~m1_subset_1(D_111, k1_zfmisc_1(k2_zfmisc_1(B_109, C_110))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.46  tff(c_677, plain, (![A_193, B_194, C_195, B_196]: (k4_tarski('#skF_6'(A_193, B_194, C_195, k1_tarski(B_196)), '#skF_7'(A_193, B_194, C_195, k1_tarski(B_196)))=A_193 | ~r2_hidden(A_193, k1_tarski(B_196)) | k2_zfmisc_1(B_194, C_195)=k1_xboole_0 | ~m1_subset_1(B_196, k2_zfmisc_1(B_194, C_195)))), inference(resolution, [status(thm)], [c_20, c_370])).
% 2.69/1.46  tff(c_93, plain, (![A_53, B_54]: (k4_tarski(k1_mcart_1(A_53), k2_mcart_1(A_53))=A_53 | ~r2_hidden(A_53, B_54) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.46  tff(c_109, plain, (![C_57]: (k4_tarski(k1_mcart_1(C_57), k2_mcart_1(C_57))=C_57 | ~v1_relat_1(k1_tarski(C_57)))), inference(resolution, [status(thm)], [c_4, c_93])).
% 2.69/1.46  tff(c_36, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.69/1.46  tff(c_121, plain, (~v1_relat_1(k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_36])).
% 2.69/1.46  tff(c_72, plain, (![A_42]: (r2_hidden('#skF_3'(A_42), A_42) | v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.46  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.46  tff(c_77, plain, (![A_1]: ('#skF_3'(k1_tarski(A_1))=A_1 | v1_relat_1(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.69/1.46  tff(c_126, plain, ('#skF_3'(k1_tarski('#skF_10'))='#skF_10'), inference(resolution, [status(thm)], [c_77, c_121])).
% 2.69/1.46  tff(c_24, plain, (![C_23, D_24, A_10]: (k4_tarski(C_23, D_24)!='#skF_3'(A_10) | v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.69/1.46  tff(c_129, plain, (![C_23, D_24]: (k4_tarski(C_23, D_24)!='#skF_10' | v1_relat_1(k1_tarski('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_24])).
% 2.69/1.46  tff(c_135, plain, (![C_23, D_24]: (k4_tarski(C_23, D_24)!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_121, c_129])).
% 2.69/1.46  tff(c_716, plain, (![A_197, B_198, B_199, C_200]: (A_197!='#skF_10' | ~r2_hidden(A_197, k1_tarski(B_198)) | k2_zfmisc_1(B_199, C_200)=k1_xboole_0 | ~m1_subset_1(B_198, k2_zfmisc_1(B_199, C_200)))), inference(superposition, [status(thm), theory('equality')], [c_677, c_135])).
% 2.69/1.46  tff(c_749, plain, (![C_201, B_202, C_203]: (C_201!='#skF_10' | k2_zfmisc_1(B_202, C_203)=k1_xboole_0 | ~m1_subset_1(C_201, k2_zfmisc_1(B_202, C_203)))), inference(resolution, [status(thm)], [c_4, c_716])).
% 2.69/1.46  tff(c_759, plain, (k2_zfmisc_1('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_749])).
% 2.69/1.46  tff(c_14, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.46  tff(c_775, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_759, c_14])).
% 2.69/1.46  tff(c_782, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_775])).
% 2.69/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.46  
% 2.69/1.46  Inference rules
% 2.69/1.46  ----------------------
% 3.10/1.46  #Ref     : 6
% 3.10/1.46  #Sup     : 186
% 3.10/1.46  #Fact    : 0
% 3.10/1.46  #Define  : 0
% 3.10/1.46  #Split   : 2
% 3.10/1.46  #Chain   : 0
% 3.10/1.46  #Close   : 0
% 3.10/1.46  
% 3.10/1.46  Ordering : KBO
% 3.10/1.46  
% 3.10/1.46  Simplification rules
% 3.10/1.46  ----------------------
% 3.10/1.46  #Subsume      : 39
% 3.10/1.46  #Demod        : 20
% 3.10/1.46  #Tautology    : 74
% 3.10/1.46  #SimpNegUnit  : 3
% 3.10/1.46  #BackRed      : 1
% 3.10/1.46  
% 3.10/1.46  #Partial instantiations: 0
% 3.10/1.46  #Strategies tried      : 1
% 3.10/1.46  
% 3.10/1.46  Timing (in seconds)
% 3.10/1.46  ----------------------
% 3.10/1.46  Preprocessing        : 0.30
% 3.10/1.46  Parsing              : 0.16
% 3.10/1.46  CNF conversion       : 0.02
% 3.10/1.46  Main loop            : 0.39
% 3.10/1.46  Inferencing          : 0.15
% 3.10/1.46  Reduction            : 0.10
% 3.10/1.46  Demodulation         : 0.06
% 3.10/1.46  BG Simplification    : 0.02
% 3.10/1.46  Subsumption          : 0.10
% 3.10/1.46  Abstraction          : 0.02
% 3.10/1.46  MUC search           : 0.00
% 3.10/1.46  Cooper               : 0.00
% 3.10/1.46  Total                : 0.72
% 3.10/1.46  Index Insertion      : 0.00
% 3.10/1.46  Index Deletion       : 0.00
% 3.10/1.46  Index Matching       : 0.00
% 3.10/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
