%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   50 (  78 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 120 expanded)
%              Number of equality atoms :   21 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_30,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_61,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden(k1_mcart_1(A_51),B_52)
      | ~ r2_hidden(A_51,k2_zfmisc_1(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_71])).

tff(c_28,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [D_37,E_38,B_33,C_34] :
      ( r2_hidden(k4_tarski(D_37,E_38),k2_zfmisc_1(B_33,C_34))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_37,E_38)),C_34)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_37,E_38)),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [D_67,E_68,B_69,C_70] :
      ( r2_hidden(k4_tarski(D_67,E_68),k2_zfmisc_1(B_69,C_70))
      | ~ r2_hidden(E_68,C_70)
      | ~ r2_hidden(D_67,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_20])).

tff(c_22,plain,(
    ! [A_39,C_41,B_40] :
      ( k2_mcart_1(A_39) = C_41
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,k1_tarski(C_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [D_67,E_68,C_41,B_69] :
      ( k2_mcart_1(k4_tarski(D_67,E_68)) = C_41
      | ~ r2_hidden(E_68,k1_tarski(C_41))
      | ~ r2_hidden(D_67,B_69) ) ),
    inference(resolution,[status(thm)],[c_107,c_22])).

tff(c_117,plain,(
    ! [E_68,C_41,D_67,B_69] :
      ( E_68 = C_41
      | ~ r2_hidden(E_68,k1_tarski(C_41))
      | ~ r2_hidden(D_67,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_111])).

tff(c_122,plain,(
    ! [D_67,B_69] : ~ r2_hidden(D_67,B_69) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_88,plain,(
    ! [A_60,C_61,B_62] :
      ( k2_mcart_1(A_60) = C_61
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,k1_tarski(C_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_75,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_93,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_78])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_93])).

tff(c_140,plain,(
    ! [E_76,C_77] :
      ( E_76 = C_77
      | ~ r2_hidden(E_76,k1_tarski(C_77)) ) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_146,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_74,c_140])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_146])).

tff(c_153,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_177,plain,(
    ! [A_86,C_87,B_88] :
      ( k2_mcart_1(A_86) = C_87
      | ~ r2_hidden(A_86,k2_zfmisc_1(B_88,k1_tarski(C_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_180,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.97/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.97/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.22  
% 1.97/1.23  tff(f_72, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.97/1.23  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.97/1.23  tff(f_65, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.97/1.23  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.97/1.23  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.97/1.23  tff(c_30, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.23  tff(c_61, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 1.97/1.23  tff(c_32, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.23  tff(c_71, plain, (![A_51, B_52, C_53]: (r2_hidden(k1_mcart_1(A_51), B_52) | ~r2_hidden(A_51, k2_zfmisc_1(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.23  tff(c_74, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_71])).
% 1.97/1.23  tff(c_28, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.97/1.23  tff(c_26, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.97/1.23  tff(c_20, plain, (![D_37, E_38, B_33, C_34]: (r2_hidden(k4_tarski(D_37, E_38), k2_zfmisc_1(B_33, C_34)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_37, E_38)), C_34) | ~r2_hidden(k1_mcart_1(k4_tarski(D_37, E_38)), B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.23  tff(c_107, plain, (![D_67, E_68, B_69, C_70]: (r2_hidden(k4_tarski(D_67, E_68), k2_zfmisc_1(B_69, C_70)) | ~r2_hidden(E_68, C_70) | ~r2_hidden(D_67, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_20])).
% 1.97/1.23  tff(c_22, plain, (![A_39, C_41, B_40]: (k2_mcart_1(A_39)=C_41 | ~r2_hidden(A_39, k2_zfmisc_1(B_40, k1_tarski(C_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.23  tff(c_111, plain, (![D_67, E_68, C_41, B_69]: (k2_mcart_1(k4_tarski(D_67, E_68))=C_41 | ~r2_hidden(E_68, k1_tarski(C_41)) | ~r2_hidden(D_67, B_69))), inference(resolution, [status(thm)], [c_107, c_22])).
% 1.97/1.23  tff(c_117, plain, (![E_68, C_41, D_67, B_69]: (E_68=C_41 | ~r2_hidden(E_68, k1_tarski(C_41)) | ~r2_hidden(D_67, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_111])).
% 1.97/1.23  tff(c_122, plain, (![D_67, B_69]: (~r2_hidden(D_67, B_69))), inference(splitLeft, [status(thm)], [c_117])).
% 1.97/1.23  tff(c_88, plain, (![A_60, C_61, B_62]: (k2_mcart_1(A_60)=C_61 | ~r2_hidden(A_60, k2_zfmisc_1(B_62, k1_tarski(C_61))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.23  tff(c_92, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_88])).
% 1.97/1.23  tff(c_75, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.23  tff(c_78, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_75])).
% 1.97/1.23  tff(c_93, plain, (r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_78])).
% 1.97/1.23  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_93])).
% 1.97/1.23  tff(c_140, plain, (![E_76, C_77]: (E_76=C_77 | ~r2_hidden(E_76, k1_tarski(C_77)))), inference(splitRight, [status(thm)], [c_117])).
% 1.97/1.23  tff(c_146, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_74, c_140])).
% 1.97/1.23  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_146])).
% 1.97/1.23  tff(c_153, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 1.97/1.23  tff(c_177, plain, (![A_86, C_87, B_88]: (k2_mcart_1(A_86)=C_87 | ~r2_hidden(A_86, k2_zfmisc_1(B_88, k1_tarski(C_87))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.23  tff(c_180, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_32, c_177])).
% 1.97/1.23  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_180])).
% 1.97/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  Inference rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Ref     : 0
% 1.97/1.23  #Sup     : 31
% 1.97/1.23  #Fact    : 0
% 1.97/1.23  #Define  : 0
% 1.97/1.23  #Split   : 2
% 1.97/1.23  #Chain   : 0
% 1.97/1.23  #Close   : 0
% 1.97/1.23  
% 1.97/1.23  Ordering : KBO
% 1.97/1.23  
% 1.97/1.23  Simplification rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Subsume      : 5
% 1.97/1.23  #Demod        : 7
% 1.97/1.23  #Tautology    : 23
% 1.97/1.23  #SimpNegUnit  : 8
% 1.97/1.23  #BackRed      : 4
% 1.97/1.23  
% 1.97/1.23  #Partial instantiations: 0
% 1.97/1.23  #Strategies tried      : 1
% 1.97/1.23  
% 1.97/1.23  Timing (in seconds)
% 1.97/1.23  ----------------------
% 1.97/1.23  Preprocessing        : 0.30
% 1.97/1.23  Parsing              : 0.15
% 1.97/1.23  CNF conversion       : 0.02
% 1.97/1.23  Main loop            : 0.13
% 1.97/1.23  Inferencing          : 0.05
% 1.97/1.23  Reduction            : 0.04
% 1.97/1.23  Demodulation         : 0.03
% 1.97/1.23  BG Simplification    : 0.01
% 1.97/1.23  Subsumption          : 0.02
% 1.97/1.23  Abstraction          : 0.01
% 1.97/1.23  MUC search           : 0.00
% 1.97/1.23  Cooper               : 0.00
% 1.97/1.23  Total                : 0.46
% 1.97/1.23  Index Insertion      : 0.00
% 1.97/1.23  Index Deletion       : 0.00
% 1.97/1.23  Index Matching       : 0.00
% 1.97/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
