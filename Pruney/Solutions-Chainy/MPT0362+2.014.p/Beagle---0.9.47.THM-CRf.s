%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   58 (  83 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 151 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_73,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_88,plain,(
    ! [B_42,A_43] :
      ( r2_hidden(B_42,A_43)
      | ~ m1_subset_1(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_209,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(B_68,A_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | v1_xboole_0(k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_223,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_209])).

tff(c_231,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_223])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_270,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,'#skF_4')
      | ~ r1_tarski(A_72,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_231,c_8])).

tff(c_297,plain,(
    ! [B_6] : r1_tarski(k3_xboole_0('#skF_5',B_6),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [B_40,A_41] :
      ( m1_subset_1(B_40,A_41)
      | ~ r2_hidden(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_598,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(k3_subset_1(A_110,C_111),k3_subset_1(A_110,B_112))
      | ~ r1_tarski(B_112,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_115,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [B_50] : k9_subset_1('#skF_4',B_50,'#skF_6') = k3_xboole_0(B_50,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_36,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k9_subset_1('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_36])).

tff(c_601,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_598,c_130])).

tff(c_606,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_601])).

tff(c_610,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_606])).

tff(c_616,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_610])).

tff(c_618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_616])).

tff(c_620,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_54,plain,(
    ! [C_32,A_33] :
      ( r2_hidden(C_32,k1_zfmisc_1(A_33))
      | ~ r1_tarski(C_32,A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_33,C_32] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_33))
      | ~ r1_tarski(C_32,A_33) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_626,plain,(
    ! [C_113] : ~ r1_tarski(C_113,'#skF_4') ),
    inference(resolution,[status(thm)],[c_620,c_62])).

tff(c_631,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.63/1.38  
% 2.63/1.38  %Foreground sorts:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Background operators:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Foreground operators:
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.63/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.63/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.38  
% 2.63/1.39  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.63/1.39  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.63/1.39  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.39  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.63/1.39  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.63/1.39  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.63/1.39  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.63/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.63/1.39  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.39  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.39  tff(c_64, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.39  tff(c_71, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.63/1.39  tff(c_73, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_71])).
% 2.63/1.39  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.39  tff(c_88, plain, (![B_42, A_43]: (r2_hidden(B_42, A_43) | ~m1_subset_1(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.39  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.39  tff(c_209, plain, (![B_68, A_69]: (r1_tarski(B_68, A_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | v1_xboole_0(k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.63/1.39  tff(c_223, plain, (r1_tarski('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_209])).
% 2.63/1.39  tff(c_231, plain, (r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_73, c_223])).
% 2.63/1.39  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.63/1.39  tff(c_270, plain, (![A_72]: (r1_tarski(A_72, '#skF_4') | ~r1_tarski(A_72, '#skF_5'))), inference(resolution, [status(thm)], [c_231, c_8])).
% 2.63/1.39  tff(c_297, plain, (![B_6]: (r1_tarski(k3_xboole_0('#skF_5', B_6), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_270])).
% 2.63/1.39  tff(c_12, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.39  tff(c_79, plain, (![B_40, A_41]: (m1_subset_1(B_40, A_41) | ~r2_hidden(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.39  tff(c_86, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_12, c_79])).
% 2.63/1.39  tff(c_598, plain, (![A_110, C_111, B_112]: (r1_tarski(k3_subset_1(A_110, C_111), k3_subset_1(A_110, B_112)) | ~r1_tarski(B_112, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.63/1.39  tff(c_115, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.63/1.39  tff(c_128, plain, (![B_50]: (k9_subset_1('#skF_4', B_50, '#skF_6')=k3_xboole_0(B_50, '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_115])).
% 2.63/1.39  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k9_subset_1('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.39  tff(c_130, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_36])).
% 2.63/1.39  tff(c_601, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_598, c_130])).
% 2.63/1.39  tff(c_606, plain, (~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_601])).
% 2.63/1.39  tff(c_610, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4')) | ~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_86, c_606])).
% 2.63/1.39  tff(c_616, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_610])).
% 2.63/1.39  tff(c_618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_616])).
% 2.63/1.39  tff(c_620, plain, (v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_71])).
% 2.63/1.39  tff(c_54, plain, (![C_32, A_33]: (r2_hidden(C_32, k1_zfmisc_1(A_33)) | ~r1_tarski(C_32, A_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.39  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.39  tff(c_62, plain, (![A_33, C_32]: (~v1_xboole_0(k1_zfmisc_1(A_33)) | ~r1_tarski(C_32, A_33))), inference(resolution, [status(thm)], [c_54, c_2])).
% 2.63/1.39  tff(c_626, plain, (![C_113]: (~r1_tarski(C_113, '#skF_4'))), inference(resolution, [status(thm)], [c_620, c_62])).
% 2.63/1.39  tff(c_631, plain, $false, inference(resolution, [status(thm)], [c_6, c_626])).
% 2.63/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.39  
% 2.63/1.39  Inference rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Ref     : 0
% 2.63/1.39  #Sup     : 121
% 2.63/1.39  #Fact    : 0
% 2.63/1.39  #Define  : 0
% 2.63/1.39  #Split   : 4
% 2.63/1.39  #Chain   : 0
% 2.63/1.39  #Close   : 0
% 2.63/1.39  
% 2.63/1.39  Ordering : KBO
% 2.63/1.39  
% 2.63/1.39  Simplification rules
% 2.63/1.39  ----------------------
% 2.63/1.39  #Subsume      : 6
% 2.63/1.39  #Demod        : 10
% 2.63/1.39  #Tautology    : 17
% 2.63/1.39  #SimpNegUnit  : 3
% 2.63/1.39  #BackRed      : 1
% 2.63/1.39  
% 2.63/1.39  #Partial instantiations: 0
% 2.63/1.39  #Strategies tried      : 1
% 2.63/1.39  
% 2.63/1.39  Timing (in seconds)
% 2.63/1.39  ----------------------
% 2.63/1.40  Preprocessing        : 0.30
% 2.63/1.40  Parsing              : 0.16
% 2.63/1.40  CNF conversion       : 0.02
% 2.63/1.40  Main loop            : 0.33
% 2.63/1.40  Inferencing          : 0.12
% 2.63/1.40  Reduction            : 0.09
% 2.63/1.40  Demodulation         : 0.06
% 2.63/1.40  BG Simplification    : 0.02
% 2.63/1.40  Subsumption          : 0.06
% 2.63/1.40  Abstraction          : 0.02
% 2.63/1.40  MUC search           : 0.00
% 2.63/1.40  Cooper               : 0.00
% 2.63/1.40  Total                : 0.66
% 2.63/1.40  Index Insertion      : 0.00
% 2.63/1.40  Index Deletion       : 0.00
% 2.63/1.40  Index Matching       : 0.00
% 2.63/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
