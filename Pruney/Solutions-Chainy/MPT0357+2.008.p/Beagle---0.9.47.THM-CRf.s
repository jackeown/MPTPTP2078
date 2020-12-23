%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 143 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  115 ( 383 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_1'(A_19,B_20),B_20)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_29,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [C_27,A_28,B_29] :
      ( r1_tarski(C_27,k3_subset_1(A_28,B_29))
      | ~ r1_tarski(B_29,k3_subset_1(A_28,C_27))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [C_27,A_28] :
      ( r1_tarski(C_27,k3_subset_1(A_28,k3_subset_1(A_28,C_27)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_28))
      | ~ m1_subset_1(k3_subset_1(A_28,C_27),k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_29,c_36])).

tff(c_111,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(k3_subset_1(A_50,C_51),k3_subset_1(A_50,B_52))
      | ~ r1_tarski(B_52,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_31,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_30,B_31,B_32] :
      ( r2_hidden('#skF_1'(A_30,B_31),B_32)
      | ~ r1_tarski(A_30,B_32)
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_33,B_34,B_35,B_36] :
      ( r2_hidden('#skF_1'(A_33,B_34),B_35)
      | ~ r1_tarski(B_36,B_35)
      | ~ r1_tarski(A_33,B_36)
      | r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_57,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),'#skF_4')
      | ~ r1_tarski(A_37,k3_subset_1('#skF_2','#skF_3'))
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_18,c_50])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_37] :
      ( ~ r1_tarski(A_37,k3_subset_1('#skF_2','#skF_3'))
      | r1_tarski(A_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_118,plain,(
    ! [C_51] :
      ( r1_tarski(k3_subset_1('#skF_2',C_51),'#skF_4')
      | ~ r1_tarski('#skF_3',C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_111,c_65])).

tff(c_142,plain,(
    ! [C_57] :
      ( r1_tarski(k3_subset_1('#skF_2',C_57),'#skF_4')
      | ~ r1_tarski('#skF_3',C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_118])).

tff(c_48,plain,(
    ! [A_30,B_31,B_2,B_32] :
      ( r2_hidden('#skF_1'(A_30,B_31),B_2)
      | ~ r1_tarski(B_32,B_2)
      | ~ r1_tarski(A_30,B_32)
      | r1_tarski(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_149,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),'#skF_4')
      | ~ r1_tarski(A_58,k3_subset_1('#skF_2',C_60))
      | r1_tarski(A_58,B_59)
      | ~ r1_tarski('#skF_3',C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_142,c_48])).

tff(c_162,plain,(
    ! [C_61,B_62] :
      ( r2_hidden('#skF_1'(k3_subset_1('#skF_2',C_61),B_62),'#skF_4')
      | r1_tarski(k3_subset_1('#skF_2',C_61),B_62)
      | ~ r1_tarski('#skF_3',C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_29,c_149])).

tff(c_196,plain,(
    ! [C_65,B_66,B_67] :
      ( r2_hidden('#skF_1'(k3_subset_1('#skF_2',C_65),B_66),B_67)
      | ~ r1_tarski('#skF_4',B_67)
      | r1_tarski(k3_subset_1('#skF_2',C_65),B_66)
      | ~ r1_tarski('#skF_3',C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_228,plain,(
    ! [B_71,C_72] :
      ( ~ r1_tarski('#skF_4',B_71)
      | r1_tarski(k3_subset_1('#skF_2',C_72),B_71)
      | ~ r1_tarski('#skF_3',C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_10,plain,(
    ! [B_9,C_11,A_8] :
      ( r1_tarski(B_9,C_11)
      | ~ r1_tarski(k3_subset_1(A_8,C_11),k3_subset_1(A_8,B_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_285,plain,(
    ! [B_76,C_77] :
      ( r1_tarski(B_76,C_77)
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski('#skF_4',k3_subset_1('#skF_2',B_76))
      | ~ r1_tarski('#skF_3',C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_228,c_10])).

tff(c_297,plain,(
    ! [C_77] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),C_77)
      | ~ r1_tarski('#skF_3',C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_40,c_285])).

tff(c_309,plain,(
    ! [C_77] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),C_77)
      | ~ r1_tarski('#skF_3',C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_297])).

tff(c_310,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_313,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_310])).

tff(c_317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_320,plain,(
    ! [C_78] :
      ( r1_tarski(k3_subset_1('#skF_2','#skF_4'),C_78)
      | ~ r1_tarski('#skF_3',C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_16,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_341,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_320,c_16])).

tff(c_353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_29,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.55/1.33  
% 2.55/1.33  %Foreground sorts:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Background operators:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Foreground operators:
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.55/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.33  
% 2.55/1.35  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_subset_1)).
% 2.55/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.55/1.35  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.55/1.35  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.55/1.35  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.55/1.35  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.35  tff(c_24, plain, (![A_19, B_20]: (~r2_hidden('#skF_1'(A_19, B_20), B_20) | r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.35  tff(c_29, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_24])).
% 2.55/1.35  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.35  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.35  tff(c_36, plain, (![C_27, A_28, B_29]: (r1_tarski(C_27, k3_subset_1(A_28, B_29)) | ~r1_tarski(B_29, k3_subset_1(A_28, C_27)) | ~m1_subset_1(C_27, k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.35  tff(c_40, plain, (![C_27, A_28]: (r1_tarski(C_27, k3_subset_1(A_28, k3_subset_1(A_28, C_27))) | ~m1_subset_1(C_27, k1_zfmisc_1(A_28)) | ~m1_subset_1(k3_subset_1(A_28, C_27), k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_29, c_36])).
% 2.55/1.35  tff(c_111, plain, (![A_50, C_51, B_52]: (r1_tarski(k3_subset_1(A_50, C_51), k3_subset_1(A_50, B_52)) | ~r1_tarski(B_52, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_50)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.35  tff(c_18, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.35  tff(c_31, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.35  tff(c_41, plain, (![A_30, B_31, B_32]: (r2_hidden('#skF_1'(A_30, B_31), B_32) | ~r1_tarski(A_30, B_32) | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_6, c_31])).
% 2.55/1.35  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.35  tff(c_50, plain, (![A_33, B_34, B_35, B_36]: (r2_hidden('#skF_1'(A_33, B_34), B_35) | ~r1_tarski(B_36, B_35) | ~r1_tarski(A_33, B_36) | r1_tarski(A_33, B_34))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.55/1.35  tff(c_57, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), '#skF_4') | ~r1_tarski(A_37, k3_subset_1('#skF_2', '#skF_3')) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_18, c_50])).
% 2.55/1.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.35  tff(c_65, plain, (![A_37]: (~r1_tarski(A_37, k3_subset_1('#skF_2', '#skF_3')) | r1_tarski(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_57, c_4])).
% 2.55/1.35  tff(c_118, plain, (![C_51]: (r1_tarski(k3_subset_1('#skF_2', C_51), '#skF_4') | ~r1_tarski('#skF_3', C_51) | ~m1_subset_1(C_51, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_111, c_65])).
% 2.55/1.35  tff(c_142, plain, (![C_57]: (r1_tarski(k3_subset_1('#skF_2', C_57), '#skF_4') | ~r1_tarski('#skF_3', C_57) | ~m1_subset_1(C_57, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_118])).
% 2.55/1.35  tff(c_48, plain, (![A_30, B_31, B_2, B_32]: (r2_hidden('#skF_1'(A_30, B_31), B_2) | ~r1_tarski(B_32, B_2) | ~r1_tarski(A_30, B_32) | r1_tarski(A_30, B_31))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.55/1.35  tff(c_149, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_1'(A_58, B_59), '#skF_4') | ~r1_tarski(A_58, k3_subset_1('#skF_2', C_60)) | r1_tarski(A_58, B_59) | ~r1_tarski('#skF_3', C_60) | ~m1_subset_1(C_60, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_142, c_48])).
% 2.55/1.35  tff(c_162, plain, (![C_61, B_62]: (r2_hidden('#skF_1'(k3_subset_1('#skF_2', C_61), B_62), '#skF_4') | r1_tarski(k3_subset_1('#skF_2', C_61), B_62) | ~r1_tarski('#skF_3', C_61) | ~m1_subset_1(C_61, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_29, c_149])).
% 2.55/1.35  tff(c_196, plain, (![C_65, B_66, B_67]: (r2_hidden('#skF_1'(k3_subset_1('#skF_2', C_65), B_66), B_67) | ~r1_tarski('#skF_4', B_67) | r1_tarski(k3_subset_1('#skF_2', C_65), B_66) | ~r1_tarski('#skF_3', C_65) | ~m1_subset_1(C_65, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_162, c_2])).
% 2.55/1.35  tff(c_228, plain, (![B_71, C_72]: (~r1_tarski('#skF_4', B_71) | r1_tarski(k3_subset_1('#skF_2', C_72), B_71) | ~r1_tarski('#skF_3', C_72) | ~m1_subset_1(C_72, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_196, c_4])).
% 2.55/1.35  tff(c_10, plain, (![B_9, C_11, A_8]: (r1_tarski(B_9, C_11) | ~r1_tarski(k3_subset_1(A_8, C_11), k3_subset_1(A_8, B_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.35  tff(c_285, plain, (![B_76, C_77]: (r1_tarski(B_76, C_77) | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_4', k3_subset_1('#skF_2', B_76)) | ~r1_tarski('#skF_3', C_77) | ~m1_subset_1(C_77, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_228, c_10])).
% 2.55/1.35  tff(c_297, plain, (![C_77]: (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), C_77) | ~r1_tarski('#skF_3', C_77) | ~m1_subset_1(C_77, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_285])).
% 2.55/1.35  tff(c_309, plain, (![C_77]: (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), C_77) | ~r1_tarski('#skF_3', C_77) | ~m1_subset_1(C_77, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_297])).
% 2.55/1.35  tff(c_310, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_309])).
% 2.55/1.35  tff(c_313, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_310])).
% 2.55/1.35  tff(c_317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 2.55/1.35  tff(c_320, plain, (![C_78]: (r1_tarski(k3_subset_1('#skF_2', '#skF_4'), C_78) | ~r1_tarski('#skF_3', C_78) | ~m1_subset_1(C_78, k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_309])).
% 2.55/1.35  tff(c_16, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.55/1.35  tff(c_341, plain, (~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_320, c_16])).
% 2.55/1.35  tff(c_353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_29, c_341])).
% 2.55/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.35  
% 2.55/1.35  Inference rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Ref     : 0
% 2.55/1.35  #Sup     : 72
% 2.55/1.35  #Fact    : 0
% 2.55/1.35  #Define  : 0
% 2.55/1.35  #Split   : 2
% 2.55/1.35  #Chain   : 0
% 2.55/1.35  #Close   : 0
% 2.55/1.35  
% 2.55/1.35  Ordering : KBO
% 2.55/1.35  
% 2.55/1.35  Simplification rules
% 2.55/1.35  ----------------------
% 2.55/1.35  #Subsume      : 14
% 2.55/1.35  #Demod        : 15
% 2.55/1.35  #Tautology    : 5
% 2.55/1.35  #SimpNegUnit  : 0
% 2.55/1.35  #BackRed      : 0
% 2.55/1.35  
% 2.55/1.35  #Partial instantiations: 0
% 2.55/1.35  #Strategies tried      : 1
% 2.55/1.35  
% 2.55/1.35  Timing (in seconds)
% 2.55/1.35  ----------------------
% 2.55/1.35  Preprocessing        : 0.28
% 2.55/1.35  Parsing              : 0.15
% 2.55/1.35  CNF conversion       : 0.02
% 2.55/1.36  Main loop            : 0.31
% 2.55/1.36  Inferencing          : 0.12
% 2.55/1.36  Reduction            : 0.07
% 2.55/1.36  Demodulation         : 0.05
% 2.55/1.36  BG Simplification    : 0.02
% 2.55/1.36  Subsumption          : 0.08
% 2.55/1.36  Abstraction          : 0.01
% 2.55/1.36  MUC search           : 0.00
% 2.55/1.36  Cooper               : 0.00
% 2.55/1.36  Total                : 0.62
% 2.55/1.36  Index Insertion      : 0.00
% 2.55/1.36  Index Deletion       : 0.00
% 2.55/1.36  Index Matching       : 0.00
% 2.55/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
