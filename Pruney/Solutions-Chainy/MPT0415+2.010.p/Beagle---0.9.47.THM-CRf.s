%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  88 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_93,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_98,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_93])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_58,C_59,B_60] :
      ( ~ r2_hidden(A_58,C_59)
      | ~ r1_xboole_0(k2_tarski(A_58,B_60),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_20,plain,(
    ! [A_34] : k1_subset_1(A_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_35] : m1_subset_1(k1_subset_1(A_35),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_42,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_118,plain,(
    ! [A_76,B_77] :
      ( k7_setfam_1(A_76,k7_setfam_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_120,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_118])).

tff(c_125,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_120])).

tff(c_183,plain,(
    ! [A_107,D_108,B_109] :
      ( r2_hidden(k3_subset_1(A_107,D_108),B_109)
      | ~ r2_hidden(D_108,k7_setfam_1(A_107,B_109))
      | ~ m1_subset_1(D_108,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(k7_setfam_1(A_107,B_109),k1_zfmisc_1(k1_zfmisc_1(A_107)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_187,plain,(
    ! [D_108] :
      ( r2_hidden(k3_subset_1('#skF_3',D_108),k1_xboole_0)
      | ~ r2_hidden(D_108,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_108,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_183])).

tff(c_193,plain,(
    ! [D_108] :
      ( r2_hidden(k3_subset_1('#skF_3',D_108),k1_xboole_0)
      | ~ r2_hidden(D_108,'#skF_4')
      | ~ m1_subset_1(D_108,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_46,c_125,c_187])).

tff(c_197,plain,(
    ! [D_110] :
      ( ~ r2_hidden(D_110,'#skF_4')
      | ~ m1_subset_1(D_110,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_193])).

tff(c_212,plain,(
    ! [A_111] : ~ r2_hidden(A_111,'#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_197])).

tff(c_216,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_212])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.30  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.07/1.30  
% 2.07/1.30  %Foreground sorts:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Background operators:
% 2.07/1.30  
% 2.07/1.30  
% 2.07/1.30  %Foreground operators:
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.30  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.07/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.07/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.07/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.30  
% 2.07/1.31  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.07/1.31  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.31  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.07/1.31  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.31  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.07/1.31  tff(f_54, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.07/1.31  tff(f_56, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.07/1.31  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.07/1.31  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.07/1.31  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.07/1.31  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.31  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.07/1.31  tff(c_93, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.28/1.31  tff(c_98, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_93])).
% 2.28/1.31  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.31  tff(c_71, plain, (![A_58, C_59, B_60]: (~r2_hidden(A_58, C_59) | ~r1_xboole_0(k2_tarski(A_58, B_60), C_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.31  tff(c_76, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.28/1.31  tff(c_20, plain, (![A_34]: (k1_subset_1(A_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.28/1.31  tff(c_22, plain, (![A_35]: (m1_subset_1(k1_subset_1(A_35), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.31  tff(c_47, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.28/1.31  tff(c_42, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.31  tff(c_118, plain, (![A_76, B_77]: (k7_setfam_1(A_76, k7_setfam_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.31  tff(c_120, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_118])).
% 2.28/1.31  tff(c_125, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_120])).
% 2.28/1.31  tff(c_183, plain, (![A_107, D_108, B_109]: (r2_hidden(k3_subset_1(A_107, D_108), B_109) | ~r2_hidden(D_108, k7_setfam_1(A_107, B_109)) | ~m1_subset_1(D_108, k1_zfmisc_1(A_107)) | ~m1_subset_1(k7_setfam_1(A_107, B_109), k1_zfmisc_1(k1_zfmisc_1(A_107))) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(A_107))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.31  tff(c_187, plain, (![D_108]: (r2_hidden(k3_subset_1('#skF_3', D_108), k1_xboole_0) | ~r2_hidden(D_108, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_108, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_125, c_183])).
% 2.28/1.31  tff(c_193, plain, (![D_108]: (r2_hidden(k3_subset_1('#skF_3', D_108), k1_xboole_0) | ~r2_hidden(D_108, '#skF_4') | ~m1_subset_1(D_108, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_46, c_125, c_187])).
% 2.28/1.31  tff(c_197, plain, (![D_110]: (~r2_hidden(D_110, '#skF_4') | ~m1_subset_1(D_110, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_76, c_193])).
% 2.28/1.31  tff(c_212, plain, (![A_111]: (~r2_hidden(A_111, '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_197])).
% 2.28/1.31  tff(c_216, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_212])).
% 2.28/1.31  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_216])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 39
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 0
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 7
% 2.28/1.31  #Demod        : 11
% 2.28/1.31  #Tautology    : 24
% 2.28/1.31  #SimpNegUnit  : 2
% 2.28/1.31  #BackRed      : 0
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.28/1.31  Preprocessing        : 0.32
% 2.28/1.31  Parsing              : 0.17
% 2.28/1.31  CNF conversion       : 0.02
% 2.28/1.31  Main loop            : 0.16
% 2.28/1.31  Inferencing          : 0.06
% 2.28/1.31  Reduction            : 0.05
% 2.28/1.31  Demodulation         : 0.04
% 2.28/1.31  BG Simplification    : 0.01
% 2.28/1.31  Subsumption          : 0.03
% 2.28/1.31  Abstraction          : 0.01
% 2.28/1.31  MUC search           : 0.00
% 2.28/1.31  Cooper               : 0.00
% 2.28/1.31  Total                : 0.51
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
