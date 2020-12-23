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
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  88 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_60,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_74,axiom,(
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

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_193,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_198,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_193])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [B_70,A_71] :
      ( ~ r2_hidden(B_70,A_71)
      | k4_xboole_0(A_71,k1_tarski(B_70)) != A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_163,plain,(
    ! [B_70] : ~ r2_hidden(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_154])).

tff(c_26,plain,(
    ! [A_36] : k1_subset_1(A_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_37] : m1_subset_1(k1_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_55,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_50,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_218,plain,(
    ! [A_88,B_89] :
      ( k7_setfam_1(A_88,k7_setfam_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_220,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_218])).

tff(c_225,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_220])).

tff(c_283,plain,(
    ! [A_119,D_120,B_121] :
      ( r2_hidden(k3_subset_1(A_119,D_120),B_121)
      | ~ r2_hidden(D_120,k7_setfam_1(A_119,B_121))
      | ~ m1_subset_1(D_120,k1_zfmisc_1(A_119))
      | ~ m1_subset_1(k7_setfam_1(A_119,B_121),k1_zfmisc_1(k1_zfmisc_1(A_119)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_287,plain,(
    ! [D_120] :
      ( r2_hidden(k3_subset_1('#skF_3',D_120),k1_xboole_0)
      | ~ r2_hidden(D_120,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_120,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_283])).

tff(c_293,plain,(
    ! [D_120] :
      ( r2_hidden(k3_subset_1('#skF_3',D_120),k1_xboole_0)
      | ~ r2_hidden(D_120,'#skF_4')
      | ~ m1_subset_1(D_120,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_225,c_287])).

tff(c_297,plain,(
    ! [D_122] :
      ( ~ r2_hidden(D_122,'#skF_4')
      | ~ m1_subset_1(D_122,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_293])).

tff(c_312,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_297])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_312])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.38  
% 2.38/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.38  %$ r2_hidden > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.38/1.38  
% 2.38/1.38  %Foreground sorts:
% 2.38/1.38  
% 2.38/1.38  
% 2.38/1.38  %Background operators:
% 2.38/1.38  
% 2.38/1.38  
% 2.38/1.38  %Foreground operators:
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.38  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.38/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.38/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.38/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.38/1.38  
% 2.38/1.39  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.38/1.39  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.38/1.39  tff(f_86, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.38/1.39  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.38/1.39  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.38/1.39  tff(f_58, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.38/1.39  tff(f_60, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.38/1.39  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.38/1.39  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.38/1.39  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.39  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.39  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.39  tff(c_193, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.38/1.39  tff(c_198, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_193])).
% 2.38/1.39  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.39  tff(c_154, plain, (![B_70, A_71]: (~r2_hidden(B_70, A_71) | k4_xboole_0(A_71, k1_tarski(B_70))!=A_71)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.39  tff(c_163, plain, (![B_70]: (~r2_hidden(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_154])).
% 2.38/1.39  tff(c_26, plain, (![A_36]: (k1_subset_1(A_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.39  tff(c_28, plain, (![A_37]: (m1_subset_1(k1_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.38/1.39  tff(c_55, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.38/1.39  tff(c_50, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.38/1.39  tff(c_218, plain, (![A_88, B_89]: (k7_setfam_1(A_88, k7_setfam_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.39  tff(c_220, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_54, c_218])).
% 2.38/1.39  tff(c_225, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_220])).
% 2.38/1.39  tff(c_283, plain, (![A_119, D_120, B_121]: (r2_hidden(k3_subset_1(A_119, D_120), B_121) | ~r2_hidden(D_120, k7_setfam_1(A_119, B_121)) | ~m1_subset_1(D_120, k1_zfmisc_1(A_119)) | ~m1_subset_1(k7_setfam_1(A_119, B_121), k1_zfmisc_1(k1_zfmisc_1(A_119))) | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_119))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.39  tff(c_287, plain, (![D_120]: (r2_hidden(k3_subset_1('#skF_3', D_120), k1_xboole_0) | ~r2_hidden(D_120, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_120, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_225, c_283])).
% 2.38/1.39  tff(c_293, plain, (![D_120]: (r2_hidden(k3_subset_1('#skF_3', D_120), k1_xboole_0) | ~r2_hidden(D_120, '#skF_4') | ~m1_subset_1(D_120, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_225, c_287])).
% 2.38/1.39  tff(c_297, plain, (![D_122]: (~r2_hidden(D_122, '#skF_4') | ~m1_subset_1(D_122, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_163, c_293])).
% 2.38/1.39  tff(c_312, plain, (![A_123]: (~r2_hidden(A_123, '#skF_4'))), inference(resolution, [status(thm)], [c_198, c_297])).
% 2.38/1.39  tff(c_316, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_312])).
% 2.38/1.39  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_316])).
% 2.38/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.39  
% 2.38/1.39  Inference rules
% 2.38/1.39  ----------------------
% 2.38/1.39  #Ref     : 0
% 2.38/1.39  #Sup     : 61
% 2.38/1.39  #Fact    : 0
% 2.38/1.39  #Define  : 0
% 2.38/1.39  #Split   : 0
% 2.38/1.39  #Chain   : 0
% 2.38/1.39  #Close   : 0
% 2.38/1.39  
% 2.38/1.39  Ordering : KBO
% 2.38/1.39  
% 2.38/1.39  Simplification rules
% 2.38/1.39  ----------------------
% 2.38/1.39  #Subsume      : 7
% 2.38/1.39  #Demod        : 12
% 2.38/1.39  #Tautology    : 44
% 2.38/1.39  #SimpNegUnit  : 2
% 2.38/1.39  #BackRed      : 0
% 2.38/1.39  
% 2.38/1.39  #Partial instantiations: 0
% 2.38/1.39  #Strategies tried      : 1
% 2.38/1.39  
% 2.38/1.39  Timing (in seconds)
% 2.38/1.39  ----------------------
% 2.38/1.40  Preprocessing        : 0.35
% 2.38/1.40  Parsing              : 0.18
% 2.38/1.40  CNF conversion       : 0.02
% 2.38/1.40  Main loop            : 0.21
% 2.38/1.40  Inferencing          : 0.08
% 2.38/1.40  Reduction            : 0.07
% 2.38/1.40  Demodulation         : 0.05
% 2.38/1.40  BG Simplification    : 0.02
% 2.38/1.40  Subsumption          : 0.03
% 2.38/1.40  Abstraction          : 0.01
% 2.38/1.40  MUC search           : 0.00
% 2.38/1.40  Cooper               : 0.00
% 2.38/1.40  Total                : 0.58
% 2.38/1.40  Index Insertion      : 0.00
% 2.38/1.40  Index Deletion       : 0.00
% 2.38/1.40  Index Matching       : 0.00
% 2.38/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
