%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   52 (  79 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 131 expanded)
%              Number of equality atoms :   28 (  69 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_73,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_36,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_67,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden(k1_mcart_1(A_55),B_56)
      | ~ r2_hidden(A_55,k2_zfmisc_1(B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_32,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [D_37,E_38,B_33,C_34] :
      ( r2_hidden(k4_tarski(D_37,E_38),k2_zfmisc_1(B_33,C_34))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_37,E_38)),C_34)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_37,E_38)),B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [D_76,E_77,B_78,C_79] :
      ( r2_hidden(k4_tarski(D_76,E_77),k2_zfmisc_1(B_78,C_79))
      | ~ r2_hidden(E_77,C_79)
      | ~ r2_hidden(D_76,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_20])).

tff(c_22,plain,(
    ! [A_39,C_41,B_40] :
      ( k2_mcart_1(A_39) = C_41
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,k1_tarski(C_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_119,plain,(
    ! [D_76,E_77,C_41,B_78] :
      ( k2_mcart_1(k4_tarski(D_76,E_77)) = C_41
      | ~ r2_hidden(E_77,k1_tarski(C_41))
      | ~ r2_hidden(D_76,B_78) ) ),
    inference(resolution,[status(thm)],[c_113,c_22])).

tff(c_125,plain,(
    ! [E_77,C_41,D_76,B_78] :
      ( E_77 = C_41
      | ~ r2_hidden(E_77,k1_tarski(C_41))
      | ~ r2_hidden(D_76,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_128,plain,(
    ! [D_76,B_78] : ~ r2_hidden(D_76,B_78) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_91,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(k2_mcart_1(A_64),C_65)
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_94,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_91])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_94])).

tff(c_151,plain,(
    ! [E_84,C_85] :
      ( E_84 = C_85
      | ~ r2_hidden(E_84,k1_tarski(C_85)) ) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_154,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_80,c_151])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_154])).

tff(c_160,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_166,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_38])).

tff(c_159,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_213,plain,(
    ! [A_109,D_110,C_111,B_112] :
      ( k2_mcart_1(A_109) = D_110
      | k2_mcart_1(A_109) = C_111
      | ~ r2_hidden(A_109,k2_zfmisc_1(B_112,k2_tarski(C_111,D_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_216,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_213])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_159,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.03/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.03/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.21  
% 2.03/1.22  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.03/1.22  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.03/1.22  tff(f_73, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.03/1.22  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_mcart_1)).
% 2.03/1.22  tff(f_61, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 2.03/1.22  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.03/1.22  tff(c_36, plain, (k2_mcart_1('#skF_1')!='#skF_4' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.03/1.22  tff(c_67, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.03/1.22  tff(c_34, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.03/1.22  tff(c_77, plain, (![A_55, B_56, C_57]: (r2_hidden(k1_mcart_1(A_55), B_56) | ~r2_hidden(A_55, k2_zfmisc_1(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.22  tff(c_80, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.03/1.22  tff(c_32, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.22  tff(c_30, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.22  tff(c_20, plain, (![D_37, E_38, B_33, C_34]: (r2_hidden(k4_tarski(D_37, E_38), k2_zfmisc_1(B_33, C_34)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_37, E_38)), C_34) | ~r2_hidden(k1_mcart_1(k4_tarski(D_37, E_38)), B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.03/1.22  tff(c_113, plain, (![D_76, E_77, B_78, C_79]: (r2_hidden(k4_tarski(D_76, E_77), k2_zfmisc_1(B_78, C_79)) | ~r2_hidden(E_77, C_79) | ~r2_hidden(D_76, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_20])).
% 2.03/1.22  tff(c_22, plain, (![A_39, C_41, B_40]: (k2_mcart_1(A_39)=C_41 | ~r2_hidden(A_39, k2_zfmisc_1(B_40, k1_tarski(C_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.03/1.22  tff(c_119, plain, (![D_76, E_77, C_41, B_78]: (k2_mcart_1(k4_tarski(D_76, E_77))=C_41 | ~r2_hidden(E_77, k1_tarski(C_41)) | ~r2_hidden(D_76, B_78))), inference(resolution, [status(thm)], [c_113, c_22])).
% 2.03/1.22  tff(c_125, plain, (![E_77, C_41, D_76, B_78]: (E_77=C_41 | ~r2_hidden(E_77, k1_tarski(C_41)) | ~r2_hidden(D_76, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_119])).
% 2.03/1.22  tff(c_128, plain, (![D_76, B_78]: (~r2_hidden(D_76, B_78))), inference(splitLeft, [status(thm)], [c_125])).
% 2.03/1.22  tff(c_91, plain, (![A_64, C_65, B_66]: (r2_hidden(k2_mcart_1(A_64), C_65) | ~r2_hidden(A_64, k2_zfmisc_1(B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.22  tff(c_94, plain, (r2_hidden(k2_mcart_1('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_91])).
% 2.03/1.22  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_94])).
% 2.03/1.22  tff(c_151, plain, (![E_84, C_85]: (E_84=C_85 | ~r2_hidden(E_84, k1_tarski(C_85)))), inference(splitRight, [status(thm)], [c_125])).
% 2.03/1.22  tff(c_154, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_80, c_151])).
% 2.03/1.22  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_154])).
% 2.03/1.22  tff(c_160, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.03/1.22  tff(c_38, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.03/1.22  tff(c_166, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_38])).
% 2.03/1.22  tff(c_159, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 2.03/1.22  tff(c_213, plain, (![A_109, D_110, C_111, B_112]: (k2_mcart_1(A_109)=D_110 | k2_mcart_1(A_109)=C_111 | ~r2_hidden(A_109, k2_zfmisc_1(B_112, k2_tarski(C_111, D_110))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.03/1.22  tff(c_216, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_213])).
% 2.03/1.22  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_159, c_216])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 37
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 2
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Subsume      : 8
% 2.03/1.22  #Demod        : 9
% 2.03/1.22  #Tautology    : 26
% 2.03/1.22  #SimpNegUnit  : 8
% 2.03/1.22  #BackRed      : 3
% 2.03/1.22  
% 2.03/1.22  #Partial instantiations: 0
% 2.03/1.22  #Strategies tried      : 1
% 2.03/1.22  
% 2.03/1.22  Timing (in seconds)
% 2.03/1.22  ----------------------
% 2.03/1.22  Preprocessing        : 0.31
% 2.03/1.22  Parsing              : 0.16
% 2.03/1.22  CNF conversion       : 0.02
% 2.03/1.22  Main loop            : 0.15
% 2.03/1.22  Inferencing          : 0.06
% 2.03/1.22  Reduction            : 0.05
% 2.03/1.22  Demodulation         : 0.04
% 2.03/1.22  BG Simplification    : 0.01
% 2.03/1.22  Subsumption          : 0.02
% 2.03/1.22  Abstraction          : 0.01
% 2.03/1.22  MUC search           : 0.00
% 2.03/1.22  Cooper               : 0.00
% 2.03/1.22  Total                : 0.49
% 2.03/1.22  Index Insertion      : 0.00
% 2.03/1.22  Index Deletion       : 0.00
% 2.03/1.22  Index Matching       : 0.00
% 2.03/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
