%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 123 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    ! [B_33,A_34] :
      ( r2_hidden(B_33,A_34)
      | ~ m1_subset_1(B_33,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [B_33,A_6] :
      ( r1_tarski(B_33,A_6)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_61,c_6])).

tff(c_69,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_65])).

tff(c_81,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_82,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k2_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [B_37,A_38] :
      ( m1_subset_1(B_37,A_38)
      | ~ r2_hidden(B_37,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_93,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_89])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_17,C_20,B_18] :
      ( r1_tarski(k3_subset_1(A_17,C_20),k3_subset_1(A_17,B_18))
      | ~ r1_tarski(B_18,C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    ! [A_52,B_53,C_54] :
      ( k4_subset_1(A_52,B_53,C_54) = k2_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_200,plain,(
    ! [B_60] :
      ( k4_subset_1('#skF_3',B_60,'#skF_5') = k2_xboole_0(B_60,'#skF_5')
      | ~ m1_subset_1(B_60,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_134])).

tff(c_217,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_200])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_219,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_34])).

tff(c_230,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_233,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2,c_230])).

tff(c_240,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_233])).

tff(c_244,plain,
    ( ~ r1_tarski('#skF_5','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_240])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_82,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.10/1.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.10/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.30  
% 2.10/1.31  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 2.10/1.31  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.10/1.31  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.31  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.10/1.31  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.10/1.31  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.31  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.10/1.31  tff(f_62, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.10/1.31  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.31  tff(c_61, plain, (![B_33, A_34]: (r2_hidden(B_33, A_34) | ~m1_subset_1(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.31  tff(c_6, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.31  tff(c_65, plain, (![B_33, A_6]: (r1_tarski(B_33, A_6) | ~m1_subset_1(B_33, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_61, c_6])).
% 2.10/1.31  tff(c_69, plain, (![B_35, A_36]: (r1_tarski(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)))), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 2.10/1.31  tff(c_81, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.10/1.31  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_82, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_69])).
% 2.10/1.31  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k2_xboole_0(A_3, C_5), B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.31  tff(c_8, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.31  tff(c_83, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~r2_hidden(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.31  tff(c_89, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_8, c_83])).
% 2.10/1.31  tff(c_93, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(negUnitSimplification, [status(thm)], [c_26, c_89])).
% 2.10/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.31  tff(c_32, plain, (![A_17, C_20, B_18]: (r1_tarski(k3_subset_1(A_17, C_20), k3_subset_1(A_17, B_18)) | ~r1_tarski(B_18, C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.31  tff(c_134, plain, (![A_52, B_53, C_54]: (k4_subset_1(A_52, B_53, C_54)=k2_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.10/1.31  tff(c_200, plain, (![B_60]: (k4_subset_1('#skF_3', B_60, '#skF_5')=k2_xboole_0(B_60, '#skF_5') | ~m1_subset_1(B_60, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_134])).
% 2.10/1.31  tff(c_217, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_200])).
% 2.10/1.31  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.31  tff(c_219, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_34])).
% 2.10/1.31  tff(c_230, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_219])).
% 2.10/1.31  tff(c_233, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2, c_230])).
% 2.10/1.31  tff(c_240, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_233])).
% 2.10/1.31  tff(c_244, plain, (~r1_tarski('#skF_5', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4, c_240])).
% 2.10/1.31  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_82, c_244])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 46
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 0
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 8
% 2.10/1.31  #Demod        : 8
% 2.10/1.31  #Tautology    : 14
% 2.10/1.31  #SimpNegUnit  : 2
% 2.10/1.31  #BackRed      : 1
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.33
% 2.10/1.31  Parsing              : 0.18
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.19
% 2.10/1.31  Inferencing          : 0.07
% 2.10/1.31  Reduction            : 0.05
% 2.10/1.31  Demodulation         : 0.03
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.03
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.55
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
