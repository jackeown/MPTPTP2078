%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:44 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  87 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36,c_48])).

tff(c_92,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_xboole_0(A_38,k4_xboole_0(C_39,B_40))
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [A_38] :
      ( r1_xboole_0(A_38,'#skF_6')
      | ~ r1_tarski(A_38,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,A_37)
      | ~ m1_subset_1(B_36,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    ! [B_36,A_9] :
      ( r1_tarski(B_36,A_9)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_84,c_10])).

tff(c_105,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(B_42,A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_88])).

tff(c_121,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_185,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k3_subset_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_204,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k3_subset_1('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_185])).

tff(c_252,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k4_xboole_0(B_60,C_61))
      | ~ r1_xboole_0(A_59,C_61)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_391,plain,(
    ! [A_71] :
      ( r1_tarski(A_71,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(A_71,'#skF_6')
      | ~ r1_tarski(A_71,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_252])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_401,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_391,c_34])).

tff(c_406,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_401])).

tff(c_409,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_98,c_406])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:15:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.38/1.29  
% 2.38/1.29  %Foreground sorts:
% 2.38/1.29  
% 2.38/1.29  
% 2.38/1.29  %Background operators:
% 2.38/1.29  
% 2.38/1.29  
% 2.38/1.29  %Foreground operators:
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.38/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.29  
% 2.38/1.31  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.38/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.38/1.31  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.38/1.31  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.38/1.31  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.38/1.31  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.38/1.31  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.38/1.31  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.38/1.31  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.31  tff(c_36, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.31  tff(c_48, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.31  tff(c_56, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_36, c_48])).
% 2.38/1.31  tff(c_92, plain, (![A_38, C_39, B_40]: (r1_xboole_0(A_38, k4_xboole_0(C_39, B_40)) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.31  tff(c_98, plain, (![A_38]: (r1_xboole_0(A_38, '#skF_6') | ~r1_tarski(A_38, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_92])).
% 2.38/1.31  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.31  tff(c_32, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.38/1.31  tff(c_84, plain, (![B_36, A_37]: (r2_hidden(B_36, A_37) | ~m1_subset_1(B_36, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.38/1.31  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.31  tff(c_88, plain, (![B_36, A_9]: (r1_tarski(B_36, A_9) | ~m1_subset_1(B_36, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_84, c_10])).
% 2.38/1.31  tff(c_105, plain, (![B_42, A_43]: (r1_tarski(B_42, A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(negUnitSimplification, [status(thm)], [c_32, c_88])).
% 2.38/1.31  tff(c_121, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_105])).
% 2.38/1.31  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.31  tff(c_185, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k3_subset_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.31  tff(c_204, plain, (k4_xboole_0('#skF_3', '#skF_6')=k3_subset_1('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_185])).
% 2.38/1.31  tff(c_252, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k4_xboole_0(B_60, C_61)) | ~r1_xboole_0(A_59, C_61) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.31  tff(c_391, plain, (![A_71]: (r1_tarski(A_71, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(A_71, '#skF_6') | ~r1_tarski(A_71, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_252])).
% 2.38/1.31  tff(c_34, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.38/1.31  tff(c_401, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_391, c_34])).
% 2.38/1.31  tff(c_406, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_401])).
% 2.38/1.31  tff(c_409, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_98, c_406])).
% 2.38/1.31  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_409])).
% 2.38/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.31  
% 2.38/1.31  Inference rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Ref     : 0
% 2.38/1.31  #Sup     : 96
% 2.38/1.31  #Fact    : 0
% 2.38/1.31  #Define  : 0
% 2.38/1.31  #Split   : 0
% 2.38/1.31  #Chain   : 0
% 2.38/1.31  #Close   : 0
% 2.38/1.31  
% 2.38/1.31  Ordering : KBO
% 2.38/1.31  
% 2.38/1.31  Simplification rules
% 2.38/1.31  ----------------------
% 2.38/1.31  #Subsume      : 12
% 2.38/1.31  #Demod        : 5
% 2.38/1.31  #Tautology    : 37
% 2.38/1.31  #SimpNegUnit  : 2
% 2.38/1.31  #BackRed      : 0
% 2.38/1.31  
% 2.38/1.31  #Partial instantiations: 0
% 2.38/1.31  #Strategies tried      : 1
% 2.38/1.31  
% 2.38/1.31  Timing (in seconds)
% 2.38/1.31  ----------------------
% 2.38/1.31  Preprocessing        : 0.31
% 2.38/1.31  Parsing              : 0.16
% 2.38/1.31  CNF conversion       : 0.02
% 2.38/1.31  Main loop            : 0.25
% 2.38/1.31  Inferencing          : 0.11
% 2.38/1.31  Reduction            : 0.07
% 2.38/1.31  Demodulation         : 0.04
% 2.38/1.31  BG Simplification    : 0.02
% 2.38/1.31  Subsumption          : 0.04
% 2.38/1.31  Abstraction          : 0.02
% 2.38/1.31  MUC search           : 0.00
% 2.38/1.31  Cooper               : 0.00
% 2.38/1.31  Total                : 0.59
% 2.38/1.31  Index Insertion      : 0.00
% 2.38/1.31  Index Deletion       : 0.00
% 2.38/1.31  Index Matching       : 0.00
% 2.38/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
