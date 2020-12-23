%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 184 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 403 expanded)
%              Number of equality atoms :   33 ( 118 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,(
    ! [B_23,A_24] :
      ( v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_53,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_49])).

tff(c_54,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( k4_tarski('#skF_1'(A_4,B_5,C_6),'#skF_2'(A_4,B_5,C_6)) = A_4
      | ~ r2_hidden(A_4,k2_zfmisc_1(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [A_33,B_34,C_35] :
      ( k4_tarski('#skF_1'(A_33,B_34,C_35),'#skF_2'(A_33,B_34,C_35)) = A_33
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13,B_14] : k2_mcart_1(k4_tarski(A_13,B_14)) = B_14 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_mcart_1(A_42) = '#skF_2'(A_42,B_43,C_44)
      | ~ r2_hidden(A_42,k2_zfmisc_1(B_43,C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_20])).

tff(c_131,plain,(
    ! [B_51,B_52,C_53] :
      ( k2_mcart_1(B_51) = '#skF_2'(B_51,B_52,C_53)
      | ~ m1_subset_1(B_51,k2_zfmisc_1(B_52,C_53))
      | v1_xboole_0(k2_zfmisc_1(B_52,C_53)) ) ),
    inference(resolution,[status(thm)],[c_10,c_96])).

tff(c_138,plain,
    ( k2_mcart_1('#skF_5') = '#skF_2'('#skF_5','#skF_3','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_142,plain,(
    k2_mcart_1('#skF_5') = '#skF_2'('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_138])).

tff(c_18,plain,(
    ! [A_13,B_14] : k1_mcart_1(k4_tarski(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_90,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_mcart_1(A_39) = '#skF_1'(A_39,B_40,C_41)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,C_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_18])).

tff(c_114,plain,(
    ! [B_48,B_49,C_50] :
      ( k1_mcart_1(B_48) = '#skF_1'(B_48,B_49,C_50)
      | ~ m1_subset_1(B_48,k2_zfmisc_1(B_49,C_50))
      | v1_xboole_0(k2_zfmisc_1(B_49,C_50)) ) ),
    inference(resolution,[status(thm)],[c_10,c_90])).

tff(c_121,plain,
    ( k1_mcart_1('#skF_5') = '#skF_1'('#skF_5','#skF_3','#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_125,plain,(
    k1_mcart_1('#skF_5') = '#skF_1'('#skF_5','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_121])).

tff(c_22,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_126,plain,(
    k4_tarski('#skF_1'('#skF_5','#skF_3','#skF_4'),k2_mcart_1('#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_22])).

tff(c_143,plain,(
    k4_tarski('#skF_1'('#skF_5','#skF_3','#skF_4'),'#skF_2'('#skF_5','#skF_3','#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_126])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_143])).

tff(c_154,plain,
    ( ~ m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_151])).

tff(c_157,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_157])).

tff(c_160,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_165,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_160,c_2])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_171,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_26])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_28])).

tff(c_161,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_169,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_177,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_169])).

tff(c_202,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_57,B_58))
      | v1_xboole_0(B_58)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_202])).

tff(c_207,plain,
    ( v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_205])).

tff(c_208,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_170,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2])).

tff(c_211,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_208,c_170])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_211])).

tff(c_216,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_220,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_216,c_170])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.29  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.94/1.29  
% 1.94/1.29  %Foreground sorts:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Background operators:
% 1.94/1.29  
% 1.94/1.29  
% 1.94/1.29  %Foreground operators:
% 1.94/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.29  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.94/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.29  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.94/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.29  
% 2.18/1.31  tff(f_79, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.18/1.31  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.18/1.31  tff(f_39, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.18/1.31  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.18/1.31  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.18/1.31  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 2.18/1.31  tff(c_24, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_49, plain, (![B_23, A_24]: (v1_xboole_0(B_23) | ~m1_subset_1(B_23, A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.31  tff(c_53, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_49])).
% 2.18/1.31  tff(c_54, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_53])).
% 2.18/1.31  tff(c_10, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.31  tff(c_6, plain, (![A_4, B_5, C_6]: (k4_tarski('#skF_1'(A_4, B_5, C_6), '#skF_2'(A_4, B_5, C_6))=A_4 | ~r2_hidden(A_4, k2_zfmisc_1(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.31  tff(c_67, plain, (![A_33, B_34, C_35]: (k4_tarski('#skF_1'(A_33, B_34, C_35), '#skF_2'(A_33, B_34, C_35))=A_33 | ~r2_hidden(A_33, k2_zfmisc_1(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.31  tff(c_20, plain, (![A_13, B_14]: (k2_mcart_1(k4_tarski(A_13, B_14))=B_14)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.31  tff(c_96, plain, (![A_42, B_43, C_44]: (k2_mcart_1(A_42)='#skF_2'(A_42, B_43, C_44) | ~r2_hidden(A_42, k2_zfmisc_1(B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_20])).
% 2.18/1.31  tff(c_131, plain, (![B_51, B_52, C_53]: (k2_mcart_1(B_51)='#skF_2'(B_51, B_52, C_53) | ~m1_subset_1(B_51, k2_zfmisc_1(B_52, C_53)) | v1_xboole_0(k2_zfmisc_1(B_52, C_53)))), inference(resolution, [status(thm)], [c_10, c_96])).
% 2.18/1.31  tff(c_138, plain, (k2_mcart_1('#skF_5')='#skF_2'('#skF_5', '#skF_3', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_131])).
% 2.18/1.31  tff(c_142, plain, (k2_mcart_1('#skF_5')='#skF_2'('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_138])).
% 2.18/1.31  tff(c_18, plain, (![A_13, B_14]: (k1_mcart_1(k4_tarski(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.31  tff(c_90, plain, (![A_39, B_40, C_41]: (k1_mcart_1(A_39)='#skF_1'(A_39, B_40, C_41) | ~r2_hidden(A_39, k2_zfmisc_1(B_40, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_18])).
% 2.18/1.31  tff(c_114, plain, (![B_48, B_49, C_50]: (k1_mcart_1(B_48)='#skF_1'(B_48, B_49, C_50) | ~m1_subset_1(B_48, k2_zfmisc_1(B_49, C_50)) | v1_xboole_0(k2_zfmisc_1(B_49, C_50)))), inference(resolution, [status(thm)], [c_10, c_90])).
% 2.18/1.31  tff(c_121, plain, (k1_mcart_1('#skF_5')='#skF_1'('#skF_5', '#skF_3', '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.18/1.31  tff(c_125, plain, (k1_mcart_1('#skF_5')='#skF_1'('#skF_5', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_121])).
% 2.18/1.31  tff(c_22, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_126, plain, (k4_tarski('#skF_1'('#skF_5', '#skF_3', '#skF_4'), k2_mcart_1('#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_22])).
% 2.18/1.31  tff(c_143, plain, (k4_tarski('#skF_1'('#skF_5', '#skF_3', '#skF_4'), '#skF_2'('#skF_5', '#skF_3', '#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_126])).
% 2.18/1.31  tff(c_151, plain, (~r2_hidden('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_143])).
% 2.18/1.31  tff(c_154, plain, (~m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_151])).
% 2.18/1.31  tff(c_157, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 2.18/1.31  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_157])).
% 2.18/1.31  tff(c_160, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_53])).
% 2.18/1.31  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.18/1.31  tff(c_165, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_160, c_2])).
% 2.18/1.31  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_171, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_26])).
% 2.18/1.31  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.31  tff(c_172, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_28])).
% 2.18/1.31  tff(c_161, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_53])).
% 2.18/1.31  tff(c_169, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_2])).
% 2.18/1.31  tff(c_177, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_169])).
% 2.18/1.31  tff(c_202, plain, (![A_57, B_58]: (~v1_xboole_0(k2_zfmisc_1(A_57, B_58)) | v1_xboole_0(B_58) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.31  tff(c_205, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_177, c_202])).
% 2.18/1.31  tff(c_207, plain, (v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_205])).
% 2.18/1.31  tff(c_208, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_207])).
% 2.18/1.31  tff(c_170, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2])).
% 2.18/1.31  tff(c_211, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_208, c_170])).
% 2.18/1.31  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_211])).
% 2.18/1.31  tff(c_216, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_207])).
% 2.18/1.31  tff(c_220, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_216, c_170])).
% 2.18/1.31  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_220])).
% 2.18/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  Inference rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Ref     : 0
% 2.18/1.31  #Sup     : 39
% 2.18/1.31  #Fact    : 0
% 2.18/1.31  #Define  : 0
% 2.18/1.31  #Split   : 2
% 2.18/1.31  #Chain   : 0
% 2.18/1.31  #Close   : 0
% 2.18/1.31  
% 2.18/1.31  Ordering : KBO
% 2.18/1.31  
% 2.18/1.31  Simplification rules
% 2.18/1.31  ----------------------
% 2.18/1.31  #Subsume      : 0
% 2.18/1.31  #Demod        : 13
% 2.18/1.31  #Tautology    : 23
% 2.18/1.31  #SimpNegUnit  : 6
% 2.18/1.31  #BackRed      : 7
% 2.18/1.31  
% 2.18/1.31  #Partial instantiations: 0
% 2.18/1.31  #Strategies tried      : 1
% 2.18/1.31  
% 2.18/1.31  Timing (in seconds)
% 2.18/1.31  ----------------------
% 2.18/1.31  Preprocessing        : 0.32
% 2.18/1.31  Parsing              : 0.17
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.18
% 2.18/1.31  Inferencing          : 0.07
% 2.18/1.31  Reduction            : 0.05
% 2.18/1.31  Demodulation         : 0.03
% 2.18/1.31  BG Simplification    : 0.01
% 2.18/1.31  Subsumption          : 0.03
% 2.18/1.31  Abstraction          : 0.01
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.53
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
