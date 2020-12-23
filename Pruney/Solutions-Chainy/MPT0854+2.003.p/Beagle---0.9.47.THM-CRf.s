%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:51 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 122 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,C))
       => ( r2_hidden(k1_mcart_1(A),B)
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_14,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6')
    | ~ r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [A_5,B_20] :
      ( k4_tarski('#skF_2'(A_5,B_20),'#skF_3'(A_5,B_20)) = B_20
      | ~ r2_hidden(B_20,A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    ! [B_44,C_45] : k4_tarski(k1_mcart_1(k4_tarski(B_44,C_45)),k2_mcart_1(k4_tarski(B_44,C_45))) = k4_tarski(B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [B_57,C_58,C_59,D_60] :
      ( r2_hidden(k1_mcart_1(k4_tarski(B_57,C_58)),C_59)
      | ~ r2_hidden(k4_tarski(B_57,C_58),k2_zfmisc_1(C_59,D_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_6])).

tff(c_3464,plain,(
    ! [A_285,B_286,C_287,D_288] :
      ( r2_hidden(k1_mcart_1(k4_tarski('#skF_2'(A_285,B_286),'#skF_3'(A_285,B_286))),C_287)
      | ~ r2_hidden(B_286,k2_zfmisc_1(C_287,D_288))
      | ~ r2_hidden(B_286,A_285)
      | ~ v1_relat_1(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_3632,plain,(
    ! [A_289] :
      ( r2_hidden(k1_mcart_1(k4_tarski('#skF_2'(A_289,'#skF_4'),'#skF_3'(A_289,'#skF_4'))),'#skF_5')
      | ~ r2_hidden('#skF_4',A_289)
      | ~ v1_relat_1(A_289) ) ),
    inference(resolution,[status(thm)],[c_20,c_3464])).

tff(c_3676,plain,(
    ! [A_5] :
      ( r2_hidden(k1_mcart_1('#skF_4'),'#skF_5')
      | ~ r2_hidden('#skF_4',A_5)
      | ~ v1_relat_1(A_5)
      | ~ r2_hidden('#skF_4',A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3632])).

tff(c_3698,plain,(
    ! [A_290] :
      ( ~ r2_hidden('#skF_4',A_290)
      | ~ v1_relat_1(A_290)
      | ~ r2_hidden('#skF_4',A_290)
      | ~ v1_relat_1(A_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3676])).

tff(c_3700,plain,
    ( ~ r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_20,c_3698])).

tff(c_3704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_3700])).

tff(c_3705,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_3709,plain,(
    ! [B_299,C_300] : k4_tarski(k1_mcart_1(k4_tarski(B_299,C_300)),k2_mcart_1(k4_tarski(B_299,C_300))) = k4_tarski(B_299,C_300) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3822,plain,(
    ! [B_327,C_328,D_329,C_330] :
      ( r2_hidden(k2_mcart_1(k4_tarski(B_327,C_328)),D_329)
      | ~ r2_hidden(k4_tarski(B_327,C_328),k2_zfmisc_1(C_330,D_329)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3709,c_4])).

tff(c_5835,plain,(
    ! [A_475,B_476,D_477,C_478] :
      ( r2_hidden(k2_mcart_1(k4_tarski('#skF_2'(A_475,B_476),'#skF_3'(A_475,B_476))),D_477)
      | ~ r2_hidden(B_476,k2_zfmisc_1(C_478,D_477))
      | ~ r2_hidden(B_476,A_475)
      | ~ v1_relat_1(A_475) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3822])).

tff(c_5987,plain,(
    ! [A_479] :
      ( r2_hidden(k2_mcart_1(k4_tarski('#skF_2'(A_479,'#skF_4'),'#skF_3'(A_479,'#skF_4'))),'#skF_6')
      | ~ r2_hidden('#skF_4',A_479)
      | ~ v1_relat_1(A_479) ) ),
    inference(resolution,[status(thm)],[c_20,c_5835])).

tff(c_6015,plain,(
    ! [A_5] :
      ( r2_hidden(k2_mcart_1('#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_4',A_5)
      | ~ v1_relat_1(A_5)
      | ~ r2_hidden('#skF_4',A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5987])).

tff(c_6029,plain,(
    ! [A_480] :
      ( ~ r2_hidden('#skF_4',A_480)
      | ~ v1_relat_1(A_480)
      | ~ r2_hidden('#skF_4',A_480)
      | ~ v1_relat_1(A_480) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3705,c_6015])).

tff(c_6031,plain,
    ( ~ r2_hidden('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_20,c_6029])).

tff(c_6035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_6031])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.50  
% 6.93/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.50  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 6.93/2.50  
% 6.93/2.50  %Foreground sorts:
% 6.93/2.50  
% 6.93/2.50  
% 6.93/2.50  %Background operators:
% 6.93/2.50  
% 6.93/2.50  
% 6.93/2.50  %Foreground operators:
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.93/2.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.93/2.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.93/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.93/2.50  tff('#skF_6', type, '#skF_6': $i).
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.93/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.93/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.93/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.93/2.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.93/2.50  
% 6.93/2.51  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.93/2.51  tff(f_55, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.93/2.51  tff(f_41, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 6.93/2.51  tff(f_48, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (k4_tarski(k1_mcart_1(A), k2_mcart_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_mcart_1)).
% 6.93/2.51  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 6.93/2.51  tff(c_14, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.51  tff(c_20, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.93/2.51  tff(c_18, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.93/2.51  tff(c_24, plain, (~r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_18])).
% 6.93/2.51  tff(c_8, plain, (![A_5, B_20]: (k4_tarski('#skF_2'(A_5, B_20), '#skF_3'(A_5, B_20))=B_20 | ~r2_hidden(B_20, A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.93/2.51  tff(c_27, plain, (![B_44, C_45]: (k4_tarski(k1_mcart_1(k4_tarski(B_44, C_45)), k2_mcart_1(k4_tarski(B_44, C_45)))=k4_tarski(B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.93/2.51  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.51  tff(c_106, plain, (![B_57, C_58, C_59, D_60]: (r2_hidden(k1_mcart_1(k4_tarski(B_57, C_58)), C_59) | ~r2_hidden(k4_tarski(B_57, C_58), k2_zfmisc_1(C_59, D_60)))), inference(superposition, [status(thm), theory('equality')], [c_27, c_6])).
% 6.93/2.51  tff(c_3464, plain, (![A_285, B_286, C_287, D_288]: (r2_hidden(k1_mcart_1(k4_tarski('#skF_2'(A_285, B_286), '#skF_3'(A_285, B_286))), C_287) | ~r2_hidden(B_286, k2_zfmisc_1(C_287, D_288)) | ~r2_hidden(B_286, A_285) | ~v1_relat_1(A_285))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 6.93/2.51  tff(c_3632, plain, (![A_289]: (r2_hidden(k1_mcart_1(k4_tarski('#skF_2'(A_289, '#skF_4'), '#skF_3'(A_289, '#skF_4'))), '#skF_5') | ~r2_hidden('#skF_4', A_289) | ~v1_relat_1(A_289))), inference(resolution, [status(thm)], [c_20, c_3464])).
% 6.93/2.51  tff(c_3676, plain, (![A_5]: (r2_hidden(k1_mcart_1('#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', A_5) | ~v1_relat_1(A_5) | ~r2_hidden('#skF_4', A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3632])).
% 6.93/2.51  tff(c_3698, plain, (![A_290]: (~r2_hidden('#skF_4', A_290) | ~v1_relat_1(A_290) | ~r2_hidden('#skF_4', A_290) | ~v1_relat_1(A_290))), inference(negUnitSimplification, [status(thm)], [c_24, c_3676])).
% 6.93/2.51  tff(c_3700, plain, (~r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_3698])).
% 6.93/2.51  tff(c_3704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_3700])).
% 6.93/2.51  tff(c_3705, plain, (~r2_hidden(k2_mcart_1('#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 6.93/2.51  tff(c_3709, plain, (![B_299, C_300]: (k4_tarski(k1_mcart_1(k4_tarski(B_299, C_300)), k2_mcart_1(k4_tarski(B_299, C_300)))=k4_tarski(B_299, C_300))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.93/2.51  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.51  tff(c_3822, plain, (![B_327, C_328, D_329, C_330]: (r2_hidden(k2_mcart_1(k4_tarski(B_327, C_328)), D_329) | ~r2_hidden(k4_tarski(B_327, C_328), k2_zfmisc_1(C_330, D_329)))), inference(superposition, [status(thm), theory('equality')], [c_3709, c_4])).
% 6.93/2.51  tff(c_5835, plain, (![A_475, B_476, D_477, C_478]: (r2_hidden(k2_mcart_1(k4_tarski('#skF_2'(A_475, B_476), '#skF_3'(A_475, B_476))), D_477) | ~r2_hidden(B_476, k2_zfmisc_1(C_478, D_477)) | ~r2_hidden(B_476, A_475) | ~v1_relat_1(A_475))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3822])).
% 6.93/2.51  tff(c_5987, plain, (![A_479]: (r2_hidden(k2_mcart_1(k4_tarski('#skF_2'(A_479, '#skF_4'), '#skF_3'(A_479, '#skF_4'))), '#skF_6') | ~r2_hidden('#skF_4', A_479) | ~v1_relat_1(A_479))), inference(resolution, [status(thm)], [c_20, c_5835])).
% 6.93/2.51  tff(c_6015, plain, (![A_5]: (r2_hidden(k2_mcart_1('#skF_4'), '#skF_6') | ~r2_hidden('#skF_4', A_5) | ~v1_relat_1(A_5) | ~r2_hidden('#skF_4', A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_5987])).
% 6.93/2.51  tff(c_6029, plain, (![A_480]: (~r2_hidden('#skF_4', A_480) | ~v1_relat_1(A_480) | ~r2_hidden('#skF_4', A_480) | ~v1_relat_1(A_480))), inference(negUnitSimplification, [status(thm)], [c_3705, c_6015])).
% 6.93/2.51  tff(c_6031, plain, (~r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_6029])).
% 6.93/2.51  tff(c_6035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_6031])).
% 6.93/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.51  
% 6.93/2.51  Inference rules
% 6.93/2.51  ----------------------
% 6.93/2.51  #Ref     : 2
% 6.93/2.51  #Sup     : 1840
% 6.93/2.51  #Fact    : 0
% 6.93/2.51  #Define  : 0
% 6.93/2.51  #Split   : 1
% 6.93/2.51  #Chain   : 0
% 6.93/2.51  #Close   : 0
% 6.93/2.51  
% 6.93/2.51  Ordering : KBO
% 6.93/2.51  
% 6.93/2.51  Simplification rules
% 6.93/2.51  ----------------------
% 6.93/2.51  #Subsume      : 54
% 6.93/2.51  #Demod        : 28
% 6.93/2.51  #Tautology    : 81
% 6.93/2.51  #SimpNegUnit  : 2
% 6.93/2.51  #BackRed      : 0
% 6.93/2.51  
% 6.93/2.51  #Partial instantiations: 0
% 6.93/2.51  #Strategies tried      : 1
% 6.93/2.51  
% 6.93/2.51  Timing (in seconds)
% 6.93/2.51  ----------------------
% 6.93/2.51  Preprocessing        : 0.28
% 6.93/2.51  Parsing              : 0.16
% 6.93/2.51  CNF conversion       : 0.02
% 6.93/2.51  Main loop            : 1.47
% 6.93/2.52  Inferencing          : 0.40
% 6.93/2.52  Reduction            : 0.39
% 6.93/2.52  Demodulation         : 0.27
% 6.93/2.52  BG Simplification    : 0.06
% 6.93/2.52  Subsumption          : 0.47
% 6.93/2.52  Abstraction          : 0.07
% 6.93/2.52  MUC search           : 0.00
% 6.93/2.52  Cooper               : 0.00
% 6.93/2.52  Total                : 1.78
% 6.93/2.52  Index Insertion      : 0.00
% 6.93/2.52  Index Deletion       : 0.00
% 6.93/2.52  Index Matching       : 0.00
% 6.93/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
