%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 120 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_44,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,k4_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,(
    ! [A_45] :
      ( r1_xboole_0(A_45,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_45,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_68,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38])).

tff(c_148,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_68])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_148])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_158,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_162,plain,(
    ! [B_49,A_7] :
      ( r1_tarski(B_49,A_7)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_158,c_6])).

tff(c_166,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_162])).

tff(c_178,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_166])).

tff(c_153,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_200,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_213,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_34,c_200])).

tff(c_316,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k3_subset_1(A_67,B_68),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k3_subset_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_516,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,k3_subset_1(A_87,B_88)) = k3_subset_1(A_87,k3_subset_1(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_316,c_26])).

tff(c_527,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_516])).

tff(c_534,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_527])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k4_xboole_0(B_5,C_6))
      | ~ r1_xboole_0(A_4,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_635,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,'#skF_5')
      | ~ r1_xboole_0(A_94,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_94,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_4])).

tff(c_641,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_635])).

tff(c_645,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_641])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.41  
% 2.57/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.57/1.41  
% 2.57/1.41  %Foreground sorts:
% 2.57/1.41  
% 2.57/1.41  
% 2.57/1.41  %Background operators:
% 2.57/1.41  
% 2.57/1.41  
% 2.57/1.41  %Foreground operators:
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.57/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.57/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.41  
% 2.79/1.42  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.79/1.42  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.79/1.42  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.79/1.42  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.79/1.42  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.79/1.42  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.79/1.42  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.79/1.42  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.79/1.42  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.79/1.42  tff(c_44, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.42  tff(c_66, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 2.79/1.42  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.42  tff(c_112, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.42  tff(c_129, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_112])).
% 2.79/1.42  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, k4_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.42  tff(c_145, plain, (![A_45]: (r1_xboole_0(A_45, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_45, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 2.79/1.42  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.42  tff(c_68, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38])).
% 2.79/1.42  tff(c_148, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_145, c_68])).
% 2.79/1.42  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_148])).
% 2.79/1.42  tff(c_154, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 2.79/1.42  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.42  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.42  tff(c_158, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.42  tff(c_6, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.42  tff(c_162, plain, (![B_49, A_7]: (r1_tarski(B_49, A_7) | ~m1_subset_1(B_49, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_158, c_6])).
% 2.79/1.42  tff(c_166, plain, (![B_51, A_52]: (r1_tarski(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)))), inference(negUnitSimplification, [status(thm)], [c_30, c_162])).
% 2.79/1.42  tff(c_178, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_166])).
% 2.79/1.42  tff(c_153, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_44])).
% 2.79/1.42  tff(c_200, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.79/1.42  tff(c_213, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_34, c_200])).
% 2.79/1.42  tff(c_316, plain, (![A_67, B_68]: (m1_subset_1(k3_subset_1(A_67, B_68), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.42  tff(c_26, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k3_subset_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.42  tff(c_516, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k3_subset_1(A_87, B_88))=k3_subset_1(A_87, k3_subset_1(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_316, c_26])).
% 2.79/1.42  tff(c_527, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_516])).
% 2.79/1.42  tff(c_534, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_527])).
% 2.79/1.42  tff(c_4, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, k4_xboole_0(B_5, C_6)) | ~r1_xboole_0(A_4, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.42  tff(c_635, plain, (![A_94]: (r1_tarski(A_94, '#skF_5') | ~r1_xboole_0(A_94, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_94, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_534, c_4])).
% 2.79/1.42  tff(c_641, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_153, c_635])).
% 2.79/1.42  tff(c_645, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_641])).
% 2.79/1.42  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_645])).
% 2.79/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  Inference rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Ref     : 0
% 2.79/1.42  #Sup     : 138
% 2.79/1.42  #Fact    : 0
% 2.79/1.42  #Define  : 0
% 2.79/1.42  #Split   : 1
% 2.79/1.42  #Chain   : 0
% 2.79/1.42  #Close   : 0
% 2.79/1.42  
% 2.79/1.42  Ordering : KBO
% 2.79/1.42  
% 2.79/1.42  Simplification rules
% 2.79/1.42  ----------------------
% 2.79/1.42  #Subsume      : 15
% 2.79/1.42  #Demod        : 22
% 2.79/1.42  #Tautology    : 63
% 2.79/1.42  #SimpNegUnit  : 9
% 2.79/1.42  #BackRed      : 0
% 2.79/1.42  
% 2.79/1.42  #Partial instantiations: 0
% 2.79/1.42  #Strategies tried      : 1
% 2.79/1.42  
% 2.79/1.42  Timing (in seconds)
% 2.79/1.42  ----------------------
% 2.79/1.42  Preprocessing        : 0.29
% 2.79/1.42  Parsing              : 0.14
% 2.79/1.42  CNF conversion       : 0.02
% 2.79/1.42  Main loop            : 0.31
% 2.79/1.43  Inferencing          : 0.12
% 2.79/1.43  Reduction            : 0.08
% 2.79/1.43  Demodulation         : 0.05
% 2.79/1.43  BG Simplification    : 0.02
% 2.79/1.43  Subsumption          : 0.06
% 2.79/1.43  Abstraction          : 0.02
% 2.79/1.43  MUC search           : 0.00
% 2.79/1.43  Cooper               : 0.00
% 2.79/1.43  Total                : 0.63
% 2.79/1.43  Index Insertion      : 0.00
% 2.79/1.43  Index Deletion       : 0.00
% 2.79/1.43  Index Matching       : 0.00
% 2.79/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
