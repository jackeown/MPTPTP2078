%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 108 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 182 expanded)
%              Number of equality atoms :   10 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_43,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_12,B_13] : ~ v1_xboole_0(k2_tarski(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_20])).

tff(c_34,plain,(
    ~ m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_100,plain,(
    ! [A_46,B_47,C_48] :
      ( m1_subset_1('#skF_3'(A_46,B_47,C_48),C_48)
      | m1_funct_2(C_48,A_46,B_47)
      | v1_xboole_0(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_31,A_1] :
      ( A_31 = A_1
      | v1_xboole_0(k1_tarski(A_1))
      | ~ m1_subset_1(A_31,k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_77,plain,(
    ! [A_31,A_1] :
      ( A_31 = A_1
      | ~ m1_subset_1(A_31,k1_tarski(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_74])).

tff(c_106,plain,(
    ! [A_46,B_47,A_1] :
      ( '#skF_3'(A_46,B_47,k1_tarski(A_1)) = A_1
      | m1_funct_2(k1_tarski(A_1),A_46,B_47)
      | v1_xboole_0(k1_tarski(A_1)) ) ),
    inference(resolution,[status(thm)],[c_100,c_77])).

tff(c_111,plain,(
    ! [A_49,B_50,A_51] :
      ( '#skF_3'(A_49,B_50,k1_tarski(A_51)) = A_51
      | m1_funct_2(k1_tarski(A_51),A_49,B_50) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_106])).

tff(c_115,plain,(
    '#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_111,c_34])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_259,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ m1_subset_1('#skF_3'(A_88,B_89,C_90),k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2('#skF_3'(A_88,B_89,C_90),A_88,B_89)
      | ~ v1_funct_1('#skF_3'(A_88,B_89,C_90))
      | m1_funct_2(C_90,A_88,B_89)
      | v1_xboole_0(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_265,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')),'#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')))
    | m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_259])).

tff(c_272,plain,
    ( m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_115,c_38,c_115,c_36,c_265])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_34,c_272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:22:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  
% 2.06/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.32  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.06/1.32  
% 2.06/1.32  %Foreground sorts:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Background operators:
% 2.06/1.32  
% 2.06/1.32  
% 2.06/1.32  %Foreground operators:
% 2.06/1.32  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.32  
% 2.06/1.33  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.33  tff(f_41, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.06/1.33  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => m1_funct_2(k1_tarski(C), A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_funct_2)).
% 2.06/1.33  tff(f_61, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_funct_2)).
% 2.06/1.33  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.06/1.33  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.33  tff(c_43, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.33  tff(c_20, plain, (![A_12, B_13]: (~v1_xboole_0(k2_tarski(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.33  tff(c_48, plain, (![A_25]: (~v1_xboole_0(k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_20])).
% 2.06/1.33  tff(c_34, plain, (~m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.33  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.33  tff(c_100, plain, (![A_46, B_47, C_48]: (m1_subset_1('#skF_3'(A_46, B_47, C_48), C_48) | m1_funct_2(C_48, A_46, B_47) | v1_xboole_0(C_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.33  tff(c_70, plain, (![A_31, B_32]: (r2_hidden(A_31, B_32) | v1_xboole_0(B_32) | ~m1_subset_1(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.33  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.33  tff(c_74, plain, (![A_31, A_1]: (A_31=A_1 | v1_xboole_0(k1_tarski(A_1)) | ~m1_subset_1(A_31, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_70, c_2])).
% 2.06/1.33  tff(c_77, plain, (![A_31, A_1]: (A_31=A_1 | ~m1_subset_1(A_31, k1_tarski(A_1)))), inference(negUnitSimplification, [status(thm)], [c_48, c_74])).
% 2.06/1.33  tff(c_106, plain, (![A_46, B_47, A_1]: ('#skF_3'(A_46, B_47, k1_tarski(A_1))=A_1 | m1_funct_2(k1_tarski(A_1), A_46, B_47) | v1_xboole_0(k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_100, c_77])).
% 2.06/1.33  tff(c_111, plain, (![A_49, B_50, A_51]: ('#skF_3'(A_49, B_50, k1_tarski(A_51))=A_51 | m1_funct_2(k1_tarski(A_51), A_49, B_50))), inference(negUnitSimplification, [status(thm)], [c_48, c_106])).
% 2.06/1.33  tff(c_115, plain, ('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_111, c_34])).
% 2.06/1.33  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.33  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.33  tff(c_259, plain, (![A_88, B_89, C_90]: (~m1_subset_1('#skF_3'(A_88, B_89, C_90), k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2('#skF_3'(A_88, B_89, C_90), A_88, B_89) | ~v1_funct_1('#skF_3'(A_88, B_89, C_90)) | m1_funct_2(C_90, A_88, B_89) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.33  tff(c_265, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6')), '#skF_4', '#skF_5') | ~v1_funct_1('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))) | m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_259])).
% 2.06/1.33  tff(c_272, plain, (m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_115, c_38, c_115, c_36, c_265])).
% 2.06/1.33  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_34, c_272])).
% 2.06/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.33  
% 2.06/1.33  Inference rules
% 2.06/1.33  ----------------------
% 2.06/1.33  #Ref     : 0
% 2.06/1.33  #Sup     : 48
% 2.06/1.33  #Fact    : 0
% 2.06/1.33  #Define  : 0
% 2.06/1.33  #Split   : 1
% 2.06/1.33  #Chain   : 0
% 2.06/1.33  #Close   : 0
% 2.06/1.33  
% 2.06/1.33  Ordering : KBO
% 2.06/1.33  
% 2.06/1.33  Simplification rules
% 2.06/1.33  ----------------------
% 2.06/1.33  #Subsume      : 2
% 2.06/1.33  #Demod        : 13
% 2.06/1.33  #Tautology    : 23
% 2.06/1.33  #SimpNegUnit  : 13
% 2.06/1.33  #BackRed      : 0
% 2.06/1.33  
% 2.06/1.33  #Partial instantiations: 0
% 2.06/1.33  #Strategies tried      : 1
% 2.06/1.33  
% 2.06/1.33  Timing (in seconds)
% 2.06/1.33  ----------------------
% 2.06/1.33  Preprocessing        : 0.32
% 2.06/1.33  Parsing              : 0.16
% 2.06/1.33  CNF conversion       : 0.02
% 2.06/1.33  Main loop            : 0.20
% 2.06/1.33  Inferencing          : 0.08
% 2.06/1.33  Reduction            : 0.06
% 2.06/1.33  Demodulation         : 0.04
% 2.06/1.33  BG Simplification    : 0.01
% 2.06/1.33  Subsumption          : 0.04
% 2.06/1.33  Abstraction          : 0.01
% 2.06/1.34  MUC search           : 0.00
% 2.06/1.34  Cooper               : 0.00
% 2.06/1.34  Total                : 0.54
% 2.06/1.34  Index Insertion      : 0.00
% 2.06/1.34  Index Deletion       : 0.00
% 2.06/1.34  Index Matching       : 0.00
% 2.06/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
