%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   45 (  95 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 182 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => m1_funct_2(k1_tarski(C),A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_funct_2)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_24,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ~ m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_113,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1('#skF_3'(A_41,B_42,C_43),C_43)
      | m1_funct_2(C_43,A_41,B_42)
      | v1_xboole_0(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [D_30,B_31,A_32] :
      ( D_30 = B_31
      | D_30 = A_32
      | ~ r2_hidden(D_30,k2_tarski(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_94,plain,(
    ! [D_33,A_34] :
      ( D_33 = A_34
      | D_33 = A_34
      | ~ r2_hidden(D_33,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_98,plain,(
    ! [A_34,A_11] :
      ( A_34 = A_11
      | v1_xboole_0(k1_tarski(A_34))
      | ~ m1_subset_1(A_11,k1_tarski(A_34)) ) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_104,plain,(
    ! [A_34,A_11] :
      ( A_34 = A_11
      | ~ m1_subset_1(A_11,k1_tarski(A_34)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_98])).

tff(c_119,plain,(
    ! [A_41,B_42,A_34] :
      ( '#skF_3'(A_41,B_42,k1_tarski(A_34)) = A_34
      | m1_funct_2(k1_tarski(A_34),A_41,B_42)
      | v1_xboole_0(k1_tarski(A_34)) ) ),
    inference(resolution,[status(thm)],[c_113,c_104])).

tff(c_124,plain,(
    ! [A_44,B_45,A_46] :
      ( '#skF_3'(A_44,B_45,k1_tarski(A_46)) = A_46
      | m1_funct_2(k1_tarski(A_46),A_44,B_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_119])).

tff(c_128,plain,(
    '#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_124,c_38])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2499,plain,(
    ! [A_3138,B_3139,C_3140] :
      ( ~ m1_subset_1('#skF_3'(A_3138,B_3139,C_3140),k1_zfmisc_1(k2_zfmisc_1(A_3138,B_3139)))
      | ~ v1_funct_2('#skF_3'(A_3138,B_3139,C_3140),A_3138,B_3139)
      | ~ v1_funct_1('#skF_3'(A_3138,B_3139,C_3140))
      | m1_funct_2(C_3140,A_3138,B_3139)
      | v1_xboole_0(C_3140) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2517,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
    | ~ v1_funct_2('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')),'#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_3'('#skF_4','#skF_5',k1_tarski('#skF_6')))
    | m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2499])).

tff(c_2525,plain,
    ( m1_funct_2(k1_tarski('#skF_6'),'#skF_4','#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_128,c_42,c_128,c_40,c_2517])).

tff(c_2527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_38,c_2525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.60  
% 3.69/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.61  %$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.69/1.61  
% 3.69/1.61  %Foreground sorts:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Background operators:
% 3.69/1.61  
% 3.69/1.61  
% 3.69/1.61  %Foreground operators:
% 3.69/1.61  tff(m1_funct_2, type, m1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.69/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.69/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.69/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.69/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.69/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.61  
% 3.69/1.62  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.69/1.62  tff(f_70, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => m1_funct_2(k1_tarski(C), A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_funct_2)).
% 3.69/1.62  tff(f_61, axiom, (![A, B, C]: (~v1_xboole_0(C) => (m1_funct_2(C, A, B) <=> (![D]: (m1_subset_1(D, C) => ((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_2)).
% 3.69/1.62  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.69/1.62  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.69/1.62  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.69/1.62  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.69/1.62  tff(c_38, plain, (~m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.62  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.62  tff(c_113, plain, (![A_41, B_42, C_43]: (m1_subset_1('#skF_3'(A_41, B_42, C_43), C_43) | m1_funct_2(C_43, A_41, B_42) | v1_xboole_0(C_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.69/1.62  tff(c_26, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.69/1.62  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.69/1.62  tff(c_75, plain, (![D_30, B_31, A_32]: (D_30=B_31 | D_30=A_32 | ~r2_hidden(D_30, k2_tarski(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.62  tff(c_94, plain, (![D_33, A_34]: (D_33=A_34 | D_33=A_34 | ~r2_hidden(D_33, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_75])).
% 3.69/1.62  tff(c_98, plain, (![A_34, A_11]: (A_34=A_11 | v1_xboole_0(k1_tarski(A_34)) | ~m1_subset_1(A_11, k1_tarski(A_34)))), inference(resolution, [status(thm)], [c_26, c_94])).
% 3.69/1.62  tff(c_104, plain, (![A_34, A_11]: (A_34=A_11 | ~m1_subset_1(A_11, k1_tarski(A_34)))), inference(negUnitSimplification, [status(thm)], [c_24, c_98])).
% 3.69/1.62  tff(c_119, plain, (![A_41, B_42, A_34]: ('#skF_3'(A_41, B_42, k1_tarski(A_34))=A_34 | m1_funct_2(k1_tarski(A_34), A_41, B_42) | v1_xboole_0(k1_tarski(A_34)))), inference(resolution, [status(thm)], [c_113, c_104])).
% 3.69/1.62  tff(c_124, plain, (![A_44, B_45, A_46]: ('#skF_3'(A_44, B_45, k1_tarski(A_46))=A_46 | m1_funct_2(k1_tarski(A_46), A_44, B_45))), inference(negUnitSimplification, [status(thm)], [c_24, c_119])).
% 3.69/1.62  tff(c_128, plain, ('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_124, c_38])).
% 3.69/1.62  tff(c_42, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.62  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.69/1.62  tff(c_2499, plain, (![A_3138, B_3139, C_3140]: (~m1_subset_1('#skF_3'(A_3138, B_3139, C_3140), k1_zfmisc_1(k2_zfmisc_1(A_3138, B_3139))) | ~v1_funct_2('#skF_3'(A_3138, B_3139, C_3140), A_3138, B_3139) | ~v1_funct_1('#skF_3'(A_3138, B_3139, C_3140)) | m1_funct_2(C_3140, A_3138, B_3139) | v1_xboole_0(C_3140))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.69/1.62  tff(c_2517, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6')), '#skF_4', '#skF_5') | ~v1_funct_1('#skF_3'('#skF_4', '#skF_5', k1_tarski('#skF_6'))) | m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2499])).
% 3.69/1.62  tff(c_2525, plain, (m1_funct_2(k1_tarski('#skF_6'), '#skF_4', '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_128, c_42, c_128, c_40, c_2517])).
% 3.69/1.62  tff(c_2527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_38, c_2525])).
% 3.69/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.62  
% 3.69/1.62  Inference rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Ref     : 0
% 3.69/1.62  #Sup     : 343
% 3.69/1.62  #Fact    : 6
% 3.69/1.62  #Define  : 0
% 3.69/1.62  #Split   : 4
% 3.69/1.62  #Chain   : 0
% 3.69/1.62  #Close   : 0
% 3.69/1.62  
% 3.69/1.62  Ordering : KBO
% 3.69/1.62  
% 3.69/1.62  Simplification rules
% 3.69/1.62  ----------------------
% 3.69/1.62  #Subsume      : 79
% 3.69/1.62  #Demod        : 93
% 3.69/1.62  #Tautology    : 92
% 3.69/1.62  #SimpNegUnit  : 21
% 3.69/1.62  #BackRed      : 0
% 3.69/1.62  
% 3.69/1.62  #Partial instantiations: 1848
% 3.69/1.62  #Strategies tried      : 1
% 3.69/1.62  
% 3.69/1.62  Timing (in seconds)
% 3.69/1.62  ----------------------
% 3.69/1.62  Preprocessing        : 0.30
% 3.69/1.62  Parsing              : 0.15
% 3.69/1.62  CNF conversion       : 0.02
% 3.69/1.62  Main loop            : 0.57
% 3.69/1.62  Inferencing          : 0.29
% 3.69/1.62  Reduction            : 0.13
% 3.69/1.62  Demodulation         : 0.09
% 3.69/1.62  BG Simplification    : 0.03
% 3.69/1.62  Subsumption          : 0.09
% 3.69/1.62  Abstraction          : 0.03
% 3.69/1.62  MUC search           : 0.00
% 3.69/1.62  Cooper               : 0.00
% 3.69/1.62  Total                : 0.90
% 3.69/1.62  Index Insertion      : 0.00
% 3.69/1.62  Index Deletion       : 0.00
% 3.69/1.62  Index Matching       : 0.00
% 3.69/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
