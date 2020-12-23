%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 (  92 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

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

tff(c_103,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_41] :
      ( r1_tarski(A_41,'#skF_3')
      | ~ r1_tarski(A_41,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_103])).

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

tff(c_722,plain,(
    ! [A_153,C_154,B_155] :
      ( r1_tarski(k3_subset_1(A_153,C_154),k3_subset_1(A_153,B_155))
      | ~ r1_tarski(B_155,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_153))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,C_63) = k3_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_209,plain,(
    ! [B_62] : k9_subset_1('#skF_3',B_62,'#skF_5') = k3_xboole_0(B_62,'#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_196])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_219,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_34])).

tff(c_730,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_722,c_219])).

tff(c_739,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2,c_730])).

tff(c_748,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_739])).

tff(c_755,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_748])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  
% 2.70/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.70/1.41  
% 2.70/1.41  %Foreground sorts:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Background operators:
% 2.70/1.41  
% 2.70/1.41  
% 2.70/1.41  %Foreground operators:
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.70/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.70/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.41  
% 2.70/1.43  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.70/1.43  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 2.70/1.43  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.70/1.43  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.70/1.43  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.70/1.43  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.70/1.43  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.70/1.43  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.70/1.43  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.43  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_26, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.43  tff(c_61, plain, (![B_33, A_34]: (r2_hidden(B_33, A_34) | ~m1_subset_1(B_33, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.43  tff(c_6, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.43  tff(c_65, plain, (![B_33, A_6]: (r1_tarski(B_33, A_6) | ~m1_subset_1(B_33, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_61, c_6])).
% 2.70/1.43  tff(c_69, plain, (![B_35, A_36]: (r1_tarski(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)))), inference(negUnitSimplification, [status(thm)], [c_26, c_65])).
% 2.70/1.43  tff(c_81, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.70/1.43  tff(c_103, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.43  tff(c_111, plain, (![A_41]: (r1_tarski(A_41, '#skF_3') | ~r1_tarski(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_103])).
% 2.70/1.43  tff(c_8, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.70/1.43  tff(c_83, plain, (![B_37, A_38]: (m1_subset_1(B_37, A_38) | ~r2_hidden(B_37, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.43  tff(c_89, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_8, c_83])).
% 2.70/1.43  tff(c_93, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(negUnitSimplification, [status(thm)], [c_26, c_89])).
% 2.70/1.43  tff(c_722, plain, (![A_153, C_154, B_155]: (r1_tarski(k3_subset_1(A_153, C_154), k3_subset_1(A_153, B_155)) | ~r1_tarski(B_155, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(A_153)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.43  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_196, plain, (![A_61, B_62, C_63]: (k9_subset_1(A_61, B_62, C_63)=k3_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.43  tff(c_209, plain, (![B_62]: (k9_subset_1('#skF_3', B_62, '#skF_5')=k3_xboole_0(B_62, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_196])).
% 2.70/1.43  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_219, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_34])).
% 2.70/1.43  tff(c_730, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_722, c_219])).
% 2.70/1.43  tff(c_739, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2, c_730])).
% 2.70/1.43  tff(c_748, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_739])).
% 2.70/1.43  tff(c_755, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_111, c_748])).
% 2.70/1.43  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_755])).
% 2.70/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  Inference rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Ref     : 0
% 2.70/1.43  #Sup     : 157
% 2.70/1.43  #Fact    : 0
% 2.70/1.43  #Define  : 0
% 2.70/1.43  #Split   : 0
% 2.70/1.43  #Chain   : 0
% 2.70/1.43  #Close   : 0
% 2.70/1.43  
% 2.70/1.43  Ordering : KBO
% 2.70/1.43  
% 2.70/1.43  Simplification rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Subsume      : 13
% 2.70/1.43  #Demod        : 28
% 2.70/1.43  #Tautology    : 39
% 2.70/1.43  #SimpNegUnit  : 2
% 2.70/1.43  #BackRed      : 1
% 2.70/1.43  
% 2.70/1.43  #Partial instantiations: 0
% 2.70/1.43  #Strategies tried      : 1
% 2.70/1.43  
% 2.70/1.43  Timing (in seconds)
% 2.70/1.43  ----------------------
% 2.70/1.43  Preprocessing        : 0.30
% 2.70/1.43  Parsing              : 0.16
% 2.70/1.43  CNF conversion       : 0.02
% 2.70/1.43  Main loop            : 0.35
% 2.70/1.43  Inferencing          : 0.14
% 2.70/1.43  Reduction            : 0.09
% 2.70/1.43  Demodulation         : 0.06
% 2.70/1.43  BG Simplification    : 0.02
% 2.70/1.43  Subsumption          : 0.07
% 2.70/1.43  Abstraction          : 0.02
% 2.70/1.43  MUC search           : 0.00
% 2.70/1.43  Cooper               : 0.00
% 2.70/1.43  Total                : 0.68
% 2.70/1.43  Index Insertion      : 0.00
% 2.70/1.43  Index Deletion       : 0.00
% 2.70/1.43  Index Matching       : 0.00
% 2.70/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
