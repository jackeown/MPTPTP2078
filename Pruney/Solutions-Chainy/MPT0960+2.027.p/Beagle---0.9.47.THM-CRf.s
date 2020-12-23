%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 102 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_72,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_54,plain,(
    ! [A_63] : v1_relat_1(k1_wellord2(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_55] :
      ( k3_relat_1(k1_wellord2(A_55)) = A_55
      | ~ v1_relat_1(k1_wellord2(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_55] : k3_relat_1(k1_wellord2(A_55)) = A_55 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_107,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(k4_tarski('#skF_7'(A_81,B_82),'#skF_8'(A_81,B_82)),A_81)
      | r1_tarski(A_81,B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_52,C_54,B_53] :
      ( r2_hidden(A_52,k3_relat_1(C_54))
      | ~ r2_hidden(k4_tarski(A_52,B_53),C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_7'(A_87,B_88),k3_relat_1(A_87))
      | r1_tarski(A_87,B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_107,c_34])).

tff(c_126,plain,(
    ! [A_55,B_88] :
      ( r2_hidden('#skF_7'(k1_wellord2(A_55),B_88),A_55)
      | r1_tarski(k1_wellord2(A_55),B_88)
      | ~ v1_relat_1(k1_wellord2(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_123])).

tff(c_128,plain,(
    ! [A_55,B_88] :
      ( r2_hidden('#skF_7'(k1_wellord2(A_55),B_88),A_55)
      | r1_tarski(k1_wellord2(A_55),B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_126])).

tff(c_32,plain,(
    ! [B_53,C_54,A_52] :
      ( r2_hidden(B_53,k3_relat_1(C_54))
      | ~ r2_hidden(k4_tarski(A_52,B_53),C_54)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_8'(A_83,B_84),k3_relat_1(A_83))
      | r1_tarski(A_83,B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_107,c_32])).

tff(c_119,plain,(
    ! [A_55,B_84] :
      ( r2_hidden('#skF_8'(k1_wellord2(A_55),B_84),A_55)
      | r1_tarski(k1_wellord2(A_55),B_84)
      | ~ v1_relat_1(k1_wellord2(A_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_116])).

tff(c_121,plain,(
    ! [A_55,B_84] :
      ( r2_hidden('#skF_8'(k1_wellord2(A_55),B_84),A_55)
      | r1_tarski(k1_wellord2(A_55),B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_119])).

tff(c_2,plain,(
    ! [E_33,F_34,A_1,B_2] :
      ( r2_hidden(k4_tarski(E_33,F_34),k2_zfmisc_1(A_1,B_2))
      | ~ r2_hidden(F_34,B_2)
      | ~ r2_hidden(E_33,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_131,plain,(
    ! [A_94,B_95] :
      ( ~ r2_hidden(k4_tarski('#skF_7'(A_94,B_95),'#skF_8'(A_94,B_95)),B_95)
      | r1_tarski(A_94,B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1256,plain,(
    ! [A_256,A_257,B_258] :
      ( r1_tarski(A_256,k2_zfmisc_1(A_257,B_258))
      | ~ v1_relat_1(A_256)
      | ~ r2_hidden('#skF_8'(A_256,k2_zfmisc_1(A_257,B_258)),B_258)
      | ~ r2_hidden('#skF_7'(A_256,k2_zfmisc_1(A_257,B_258)),A_257) ) ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_1295,plain,(
    ! [A_55,A_257] :
      ( ~ v1_relat_1(k1_wellord2(A_55))
      | ~ r2_hidden('#skF_7'(k1_wellord2(A_55),k2_zfmisc_1(A_257,A_55)),A_257)
      | r1_tarski(k1_wellord2(A_55),k2_zfmisc_1(A_257,A_55)) ) ),
    inference(resolution,[status(thm)],[c_121,c_1256])).

tff(c_1315,plain,(
    ! [A_259,A_260] :
      ( ~ r2_hidden('#skF_7'(k1_wellord2(A_259),k2_zfmisc_1(A_260,A_259)),A_260)
      | r1_tarski(k1_wellord2(A_259),k2_zfmisc_1(A_260,A_259)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1295])).

tff(c_1388,plain,(
    ! [A_55] : r1_tarski(k1_wellord2(A_55),k2_zfmisc_1(A_55,A_55)) ),
    inference(resolution,[status(thm)],[c_128,c_1315])).

tff(c_56,plain,(
    ~ r1_tarski(k1_wellord2('#skF_11'),k2_zfmisc_1('#skF_11','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  
% 3.55/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.59  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9
% 3.55/1.59  
% 3.55/1.59  %Foreground sorts:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Background operators:
% 3.55/1.59  
% 3.55/1.59  
% 3.55/1.59  %Foreground operators:
% 3.55/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.59  tff('#skF_11', type, '#skF_11': $i).
% 3.55/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.55/1.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.55/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.55/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.59  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.55/1.59  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.55/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.55/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.55/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.55/1.59  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.55/1.59  
% 3.55/1.60  tff(f_72, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.55/1.60  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.55/1.60  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 3.55/1.60  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 3.55/1.60  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.55/1.60  tff(f_75, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 3.55/1.60  tff(c_54, plain, (![A_63]: (v1_relat_1(k1_wellord2(A_63)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.55/1.60  tff(c_48, plain, (![A_55]: (k3_relat_1(k1_wellord2(A_55))=A_55 | ~v1_relat_1(k1_wellord2(A_55)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.55/1.60  tff(c_62, plain, (![A_55]: (k3_relat_1(k1_wellord2(A_55))=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 3.55/1.60  tff(c_107, plain, (![A_81, B_82]: (r2_hidden(k4_tarski('#skF_7'(A_81, B_82), '#skF_8'(A_81, B_82)), A_81) | r1_tarski(A_81, B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.60  tff(c_34, plain, (![A_52, C_54, B_53]: (r2_hidden(A_52, k3_relat_1(C_54)) | ~r2_hidden(k4_tarski(A_52, B_53), C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.60  tff(c_123, plain, (![A_87, B_88]: (r2_hidden('#skF_7'(A_87, B_88), k3_relat_1(A_87)) | r1_tarski(A_87, B_88) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_107, c_34])).
% 3.55/1.60  tff(c_126, plain, (![A_55, B_88]: (r2_hidden('#skF_7'(k1_wellord2(A_55), B_88), A_55) | r1_tarski(k1_wellord2(A_55), B_88) | ~v1_relat_1(k1_wellord2(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_123])).
% 3.55/1.60  tff(c_128, plain, (![A_55, B_88]: (r2_hidden('#skF_7'(k1_wellord2(A_55), B_88), A_55) | r1_tarski(k1_wellord2(A_55), B_88))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_126])).
% 3.55/1.60  tff(c_32, plain, (![B_53, C_54, A_52]: (r2_hidden(B_53, k3_relat_1(C_54)) | ~r2_hidden(k4_tarski(A_52, B_53), C_54) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.60  tff(c_116, plain, (![A_83, B_84]: (r2_hidden('#skF_8'(A_83, B_84), k3_relat_1(A_83)) | r1_tarski(A_83, B_84) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_107, c_32])).
% 3.55/1.60  tff(c_119, plain, (![A_55, B_84]: (r2_hidden('#skF_8'(k1_wellord2(A_55), B_84), A_55) | r1_tarski(k1_wellord2(A_55), B_84) | ~v1_relat_1(k1_wellord2(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_116])).
% 3.55/1.60  tff(c_121, plain, (![A_55, B_84]: (r2_hidden('#skF_8'(k1_wellord2(A_55), B_84), A_55) | r1_tarski(k1_wellord2(A_55), B_84))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_119])).
% 3.55/1.60  tff(c_2, plain, (![E_33, F_34, A_1, B_2]: (r2_hidden(k4_tarski(E_33, F_34), k2_zfmisc_1(A_1, B_2)) | ~r2_hidden(F_34, B_2) | ~r2_hidden(E_33, A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.55/1.60  tff(c_131, plain, (![A_94, B_95]: (~r2_hidden(k4_tarski('#skF_7'(A_94, B_95), '#skF_8'(A_94, B_95)), B_95) | r1_tarski(A_94, B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.55/1.60  tff(c_1256, plain, (![A_256, A_257, B_258]: (r1_tarski(A_256, k2_zfmisc_1(A_257, B_258)) | ~v1_relat_1(A_256) | ~r2_hidden('#skF_8'(A_256, k2_zfmisc_1(A_257, B_258)), B_258) | ~r2_hidden('#skF_7'(A_256, k2_zfmisc_1(A_257, B_258)), A_257))), inference(resolution, [status(thm)], [c_2, c_131])).
% 3.55/1.60  tff(c_1295, plain, (![A_55, A_257]: (~v1_relat_1(k1_wellord2(A_55)) | ~r2_hidden('#skF_7'(k1_wellord2(A_55), k2_zfmisc_1(A_257, A_55)), A_257) | r1_tarski(k1_wellord2(A_55), k2_zfmisc_1(A_257, A_55)))), inference(resolution, [status(thm)], [c_121, c_1256])).
% 3.55/1.60  tff(c_1315, plain, (![A_259, A_260]: (~r2_hidden('#skF_7'(k1_wellord2(A_259), k2_zfmisc_1(A_260, A_259)), A_260) | r1_tarski(k1_wellord2(A_259), k2_zfmisc_1(A_260, A_259)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1295])).
% 3.55/1.60  tff(c_1388, plain, (![A_55]: (r1_tarski(k1_wellord2(A_55), k2_zfmisc_1(A_55, A_55)))), inference(resolution, [status(thm)], [c_128, c_1315])).
% 3.55/1.60  tff(c_56, plain, (~r1_tarski(k1_wellord2('#skF_11'), k2_zfmisc_1('#skF_11', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.55/1.60  tff(c_1394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1388, c_56])).
% 3.55/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.60  
% 3.55/1.60  Inference rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Ref     : 0
% 3.55/1.60  #Sup     : 314
% 3.55/1.60  #Fact    : 0
% 3.55/1.60  #Define  : 0
% 3.55/1.60  #Split   : 0
% 3.55/1.60  #Chain   : 0
% 3.55/1.60  #Close   : 0
% 3.55/1.60  
% 3.55/1.60  Ordering : KBO
% 3.55/1.60  
% 3.55/1.60  Simplification rules
% 3.55/1.60  ----------------------
% 3.55/1.60  #Subsume      : 25
% 3.55/1.60  #Demod        : 78
% 3.55/1.60  #Tautology    : 23
% 3.55/1.60  #SimpNegUnit  : 0
% 3.55/1.60  #BackRed      : 1
% 3.55/1.60  
% 3.55/1.60  #Partial instantiations: 0
% 3.55/1.60  #Strategies tried      : 1
% 3.55/1.60  
% 3.55/1.60  Timing (in seconds)
% 3.55/1.60  ----------------------
% 3.55/1.61  Preprocessing        : 0.30
% 3.55/1.61  Parsing              : 0.15
% 3.55/1.61  CNF conversion       : 0.03
% 3.55/1.61  Main loop            : 0.54
% 3.55/1.61  Inferencing          : 0.19
% 3.55/1.61  Reduction            : 0.12
% 3.55/1.61  Demodulation         : 0.09
% 3.55/1.61  BG Simplification    : 0.04
% 3.55/1.61  Subsumption          : 0.16
% 3.55/1.61  Abstraction          : 0.03
% 3.55/1.61  MUC search           : 0.00
% 3.55/1.61  Cooper               : 0.00
% 3.55/1.61  Total                : 0.87
% 3.55/1.61  Index Insertion      : 0.00
% 3.55/1.61  Index Deletion       : 0.00
% 3.55/1.61  Index Matching       : 0.00
% 3.55/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
