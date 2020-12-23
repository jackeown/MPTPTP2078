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
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  94 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [D_30,A_31,B_32] :
      ( r2_hidden(D_30,A_31)
      | ~ r2_hidden(D_30,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_332,plain,(
    ! [A_81,B_82,B_83] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_81,B_82),B_83),A_81)
      | r1_tarski(k3_xboole_0(A_81,B_82),B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_350,plain,(
    ! [A_81,B_82] : r1_tarski(k3_xboole_0(A_81,B_82),A_81) ),
    inference(resolution,[status(thm)],[c_332,c_4])).

tff(c_40,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_102,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    ! [B_54] : k9_subset_1('#skF_4',B_54,'#skF_6') = k3_xboole_0(B_54,'#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k9_subset_1(A_18,B_19,C_20),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_132,plain,(
    ! [B_54] :
      ( m1_subset_1(k3_xboole_0(B_54,'#skF_6'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_30])).

tff(c_140,plain,(
    ! [B_55] : m1_subset_1(k3_xboole_0(B_55,'#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_147,plain,(
    ! [B_55] : k4_xboole_0('#skF_4',k3_xboole_0(B_55,'#skF_6')) = k3_subset_1('#skF_4',k3_xboole_0(B_55,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_112,plain,(
    ! [A_50,D_51,B_52,C_53] :
      ( r1_tarski(k4_xboole_0(A_50,D_51),k4_xboole_0(B_52,C_53))
      | ~ r1_tarski(C_53,D_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_420,plain,(
    ! [B_95,C_96] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),k4_xboole_0(B_95,C_96))
      | ~ r1_tarski(C_96,'#skF_5')
      | ~ r1_tarski('#skF_4',B_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_112])).

tff(c_426,plain,(
    ! [B_55] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0(B_55,'#skF_6')))
      | ~ r1_tarski(k3_xboole_0(B_55,'#skF_6'),'#skF_5')
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_420])).

tff(c_528,plain,(
    ! [B_114] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0(B_114,'#skF_6')))
      | ~ r1_tarski(k3_xboole_0(B_114,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_426])).

tff(c_110,plain,(
    ! [B_48] : k9_subset_1('#skF_4',B_48,'#skF_6') = k3_xboole_0(B_48,'#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_34,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k9_subset_1('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_125,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_34])).

tff(c_531,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_528,c_125])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_531])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  
% 2.75/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.75/1.46  
% 2.75/1.46  %Foreground sorts:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Background operators:
% 2.75/1.46  
% 2.75/1.46  
% 2.75/1.46  %Foreground operators:
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.75/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.75/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.75/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.46  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.75/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.46  
% 2.75/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.48  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.75/1.48  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.75/1.48  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.75/1.48  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.75/1.48  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.75/1.48  tff(f_47, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 2.75/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.48  tff(c_47, plain, (![D_30, A_31, B_32]: (r2_hidden(D_30, A_31) | ~r2_hidden(D_30, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.48  tff(c_332, plain, (![A_81, B_82, B_83]: (r2_hidden('#skF_1'(k3_xboole_0(A_81, B_82), B_83), A_81) | r1_tarski(k3_xboole_0(A_81, B_82), B_83))), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.75/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.48  tff(c_350, plain, (![A_81, B_82]: (r1_tarski(k3_xboole_0(A_81, B_82), A_81))), inference(resolution, [status(thm)], [c_332, c_4])).
% 2.75/1.48  tff(c_40, plain, (![A_27, B_28]: (~r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.48  tff(c_45, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_40])).
% 2.75/1.48  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.48  tff(c_102, plain, (![A_47, B_48, C_49]: (k9_subset_1(A_47, B_48, C_49)=k3_xboole_0(B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.75/1.48  tff(c_126, plain, (![B_54]: (k9_subset_1('#skF_4', B_54, '#skF_6')=k3_xboole_0(B_54, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_102])).
% 2.75/1.48  tff(c_30, plain, (![A_18, B_19, C_20]: (m1_subset_1(k9_subset_1(A_18, B_19, C_20), k1_zfmisc_1(A_18)) | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.48  tff(c_132, plain, (![B_54]: (m1_subset_1(k3_xboole_0(B_54, '#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_30])).
% 2.75/1.48  tff(c_140, plain, (![B_55]: (m1_subset_1(k3_xboole_0(B_55, '#skF_6'), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_132])).
% 2.75/1.48  tff(c_28, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.48  tff(c_147, plain, (![B_55]: (k4_xboole_0('#skF_4', k3_xboole_0(B_55, '#skF_6'))=k3_subset_1('#skF_4', k3_xboole_0(B_55, '#skF_6')))), inference(resolution, [status(thm)], [c_140, c_28])).
% 2.75/1.48  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.48  tff(c_63, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.75/1.48  tff(c_71, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_63])).
% 2.75/1.48  tff(c_112, plain, (![A_50, D_51, B_52, C_53]: (r1_tarski(k4_xboole_0(A_50, D_51), k4_xboole_0(B_52, C_53)) | ~r1_tarski(C_53, D_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.75/1.48  tff(c_420, plain, (![B_95, C_96]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k4_xboole_0(B_95, C_96)) | ~r1_tarski(C_96, '#skF_5') | ~r1_tarski('#skF_4', B_95))), inference(superposition, [status(thm), theory('equality')], [c_71, c_112])).
% 2.75/1.48  tff(c_426, plain, (![B_55]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0(B_55, '#skF_6'))) | ~r1_tarski(k3_xboole_0(B_55, '#skF_6'), '#skF_5') | ~r1_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_420])).
% 2.75/1.48  tff(c_528, plain, (![B_114]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0(B_114, '#skF_6'))) | ~r1_tarski(k3_xboole_0(B_114, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_426])).
% 2.75/1.48  tff(c_110, plain, (![B_48]: (k9_subset_1('#skF_4', B_48, '#skF_6')=k3_xboole_0(B_48, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_102])).
% 2.75/1.48  tff(c_34, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k9_subset_1('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.75/1.48  tff(c_125, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_34])).
% 2.75/1.48  tff(c_531, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_528, c_125])).
% 2.75/1.48  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_350, c_531])).
% 2.75/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.48  
% 2.75/1.48  Inference rules
% 2.75/1.48  ----------------------
% 2.75/1.48  #Ref     : 0
% 2.75/1.48  #Sup     : 109
% 2.75/1.48  #Fact    : 0
% 2.75/1.48  #Define  : 0
% 2.75/1.48  #Split   : 2
% 2.75/1.48  #Chain   : 0
% 2.75/1.48  #Close   : 0
% 2.75/1.48  
% 2.75/1.48  Ordering : KBO
% 2.75/1.48  
% 2.75/1.48  Simplification rules
% 2.75/1.48  ----------------------
% 2.75/1.48  #Subsume      : 4
% 2.75/1.48  #Demod        : 31
% 2.75/1.48  #Tautology    : 23
% 2.75/1.48  #SimpNegUnit  : 0
% 2.75/1.48  #BackRed      : 1
% 2.75/1.48  
% 2.75/1.48  #Partial instantiations: 0
% 2.75/1.48  #Strategies tried      : 1
% 2.75/1.48  
% 2.75/1.48  Timing (in seconds)
% 2.75/1.48  ----------------------
% 2.75/1.48  Preprocessing        : 0.32
% 2.75/1.48  Parsing              : 0.17
% 2.75/1.48  CNF conversion       : 0.03
% 2.75/1.48  Main loop            : 0.30
% 2.75/1.48  Inferencing          : 0.11
% 2.75/1.48  Reduction            : 0.08
% 2.75/1.48  Demodulation         : 0.06
% 2.75/1.48  BG Simplification    : 0.02
% 2.75/1.48  Subsumption          : 0.07
% 2.75/1.48  Abstraction          : 0.02
% 2.75/1.48  MUC search           : 0.00
% 2.75/1.48  Cooper               : 0.00
% 2.75/1.48  Total                : 0.66
% 2.75/1.48  Index Insertion      : 0.00
% 2.75/1.48  Index Deletion       : 0.00
% 2.75/1.48  Index Matching       : 0.00
% 2.75/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
