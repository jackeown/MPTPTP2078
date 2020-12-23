%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  88 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_24])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_84,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_114,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_123,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_114])).

tff(c_126,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_123])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_7,B_8] : k4_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_180,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(A_44,B_43)
      | ~ v1_zfmisc_1(B_43)
      | v1_xboole_0(B_43)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_248,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ v1_zfmisc_1(B_53)
      | v1_xboole_0(B_53)
      | v1_xboole_0(A_54)
      | k4_xboole_0(A_54,B_53) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_250,plain,(
    ! [A_54] :
      ( A_54 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_54)
      | k4_xboole_0(A_54,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_248])).

tff(c_254,plain,(
    ! [A_55] :
      ( A_55 = '#skF_1'
      | v1_xboole_0(A_55)
      | k4_xboole_0(A_55,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_250])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_254,c_26])).

tff(c_263,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_257])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_12])).

tff(c_295,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_281])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:51:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.18  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.18  
% 1.68/1.18  %Foreground sorts:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Background operators:
% 1.68/1.18  
% 1.68/1.18  
% 1.68/1.18  %Foreground operators:
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.68/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.68/1.18  
% 1.97/1.19  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.97/1.19  tff(f_72, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.97/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.97/1.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.97/1.19  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.97/1.19  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.97/1.19  tff(f_60, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.97/1.19  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | k4_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.19  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.19  tff(c_38, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_24])).
% 1.97/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.19  tff(c_39, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.19  tff(c_51, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.97/1.19  tff(c_84, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.19  tff(c_96, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_84])).
% 1.97/1.19  tff(c_114, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.19  tff(c_123, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_96, c_114])).
% 1.97/1.19  tff(c_126, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_123])).
% 1.97/1.19  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.19  tff(c_50, plain, (![A_7, B_8]: (k4_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_39])).
% 1.97/1.19  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.19  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.19  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.19  tff(c_180, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(A_44, B_43) | ~v1_zfmisc_1(B_43) | v1_xboole_0(B_43) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.19  tff(c_248, plain, (![B_53, A_54]: (B_53=A_54 | ~v1_zfmisc_1(B_53) | v1_xboole_0(B_53) | v1_xboole_0(A_54) | k4_xboole_0(A_54, B_53)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_180])).
% 1.97/1.19  tff(c_250, plain, (![A_54]: (A_54='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_54) | k4_xboole_0(A_54, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_248])).
% 1.97/1.19  tff(c_254, plain, (![A_55]: (A_55='#skF_1' | v1_xboole_0(A_55) | k4_xboole_0(A_55, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_250])).
% 1.97/1.19  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.19  tff(c_257, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_254, c_26])).
% 1.97/1.19  tff(c_263, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_257])).
% 1.97/1.19  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.19  tff(c_281, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_263, c_12])).
% 1.97/1.19  tff(c_295, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_281])).
% 1.97/1.19  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_295])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 59
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 0
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 2
% 1.97/1.19  #Demod        : 36
% 1.97/1.19  #Tautology    : 40
% 1.97/1.19  #SimpNegUnit  : 2
% 1.97/1.19  #BackRed      : 1
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.19  Preprocessing        : 0.29
% 1.97/1.19  Parsing              : 0.15
% 1.97/1.19  CNF conversion       : 0.02
% 1.97/1.19  Main loop            : 0.16
% 1.97/1.19  Inferencing          : 0.06
% 1.97/1.19  Reduction            : 0.05
% 1.97/1.19  Demodulation         : 0.04
% 1.97/1.19  BG Simplification    : 0.01
% 1.97/1.19  Subsumption          : 0.03
% 1.97/1.19  Abstraction          : 0.01
% 1.97/1.19  MUC search           : 0.00
% 1.97/1.19  Cooper               : 0.00
% 1.97/1.19  Total                : 0.47
% 1.97/1.19  Index Insertion      : 0.00
% 1.97/1.19  Index Deletion       : 0.00
% 1.97/1.19  Index Matching       : 0.00
% 1.97/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
