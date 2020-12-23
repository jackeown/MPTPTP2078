%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   53 (  96 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 200 expanded)
%              Number of equality atoms :   54 ( 104 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_66,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_635,plain,(
    ! [A_129,B_130] :
      ( r2_hidden(k4_tarski('#skF_1'(A_129,B_130),'#skF_2'(A_129,B_130)),A_129)
      | r2_hidden('#skF_3'(A_129,B_130),B_130)
      | k1_relat_1(A_129) = B_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_52,B_53] : ~ r2_hidden(A_52,k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_79,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_719,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_131),B_131)
      | k1_relat_1(k1_xboole_0) = B_131 ) ),
    inference(resolution,[status(thm)],[c_635,c_79])).

tff(c_799,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_719,c_79])).

tff(c_718,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_130),B_130)
      | k1_relat_1(k1_xboole_0) = B_130 ) ),
    inference(resolution,[status(thm)],[c_635,c_79])).

tff(c_820,plain,(
    ! [B_130] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_130),B_130)
      | k1_xboole_0 = B_130 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_718])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_845,plain,(
    ! [B_135] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_135),B_135)
      | k1_xboole_0 = B_135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_718])).

tff(c_26,plain,(
    ! [A_24,B_25] : v1_funct_1('#skF_5'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_24,B_25] : k1_relat_1('#skF_5'(A_24,B_25)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [A_24,B_25] : v1_relat_1('#skF_5'(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [A_31] : v1_funct_1('#skF_6'(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_31] : k1_relat_1('#skF_6'(A_31)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_31] : v1_relat_1('#skF_6'(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,(
    ! [C_54,B_55] :
      ( C_54 = B_55
      | k1_relat_1(C_54) != '#skF_7'
      | k1_relat_1(B_55) != '#skF_7'
      | ~ v1_funct_1(C_54)
      | ~ v1_relat_1(C_54)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,(
    ! [B_55,A_31] :
      ( B_55 = '#skF_6'(A_31)
      | k1_relat_1('#skF_6'(A_31)) != '#skF_7'
      | k1_relat_1(B_55) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_31))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_36,c_83])).

tff(c_135,plain,(
    ! [B_69,A_70] :
      ( B_69 = '#skF_6'(A_70)
      | A_70 != '#skF_7'
      | k1_relat_1(B_69) != '#skF_7'
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_87])).

tff(c_137,plain,(
    ! [A_70,A_24,B_25] :
      ( '#skF_6'(A_70) = '#skF_5'(A_24,B_25)
      | A_70 != '#skF_7'
      | k1_relat_1('#skF_5'(A_24,B_25)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_24,B_25)) ) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_217,plain,(
    ! [A_78,A_79,B_80] :
      ( '#skF_6'(A_78) = '#skF_5'(A_79,B_80)
      | A_78 != '#skF_7'
      | A_79 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_137])).

tff(c_22,plain,(
    ! [A_24,B_25,D_30] :
      ( k1_funct_1('#skF_5'(A_24,B_25),D_30) = B_25
      | ~ r2_hidden(D_30,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_232,plain,(
    ! [A_78,D_30,B_80,A_79] :
      ( k1_funct_1('#skF_6'(A_78),D_30) = B_80
      | ~ r2_hidden(D_30,A_79)
      | A_78 != '#skF_7'
      | A_79 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_22])).

tff(c_1194,plain,(
    ! [A_145,B_146] :
      ( k1_funct_1('#skF_6'(A_145),'#skF_3'(k1_xboole_0,B_146)) = '#skF_7'
      | A_145 != '#skF_7'
      | B_146 != '#skF_7'
      | k1_xboole_0 = B_146 ) ),
    inference(resolution,[status(thm)],[c_845,c_232])).

tff(c_30,plain,(
    ! [A_31,C_36] :
      ( k1_funct_1('#skF_6'(A_31),C_36) = k1_xboole_0
      | ~ r2_hidden(C_36,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1197,plain,(
    ! [B_146,A_145] :
      ( k1_xboole_0 = '#skF_7'
      | ~ r2_hidden('#skF_3'(k1_xboole_0,B_146),A_145)
      | A_145 != '#skF_7'
      | B_146 != '#skF_7'
      | k1_xboole_0 = B_146 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_30])).

tff(c_1356,plain,(
    ! [B_980,A_981] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0,B_980),A_981)
      | A_981 != '#skF_7'
      | B_980 != '#skF_7'
      | k1_xboole_0 = B_980 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1197])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_820,c_1356])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.65  
% 3.49/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.65  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 3.49/1.65  
% 3.49/1.65  %Foreground sorts:
% 3.49/1.65  
% 3.49/1.65  
% 3.49/1.65  %Background operators:
% 3.49/1.65  
% 3.49/1.65  
% 3.49/1.65  %Foreground operators:
% 3.49/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.49/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.49/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.49/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.49/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.49/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.49/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.49/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.49/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.49/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.65  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.49/1.65  
% 3.86/1.66  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.86/1.66  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.86/1.66  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.86/1.66  tff(f_85, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 3.86/1.66  tff(f_54, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.86/1.66  tff(f_66, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.86/1.66  tff(c_635, plain, (![A_129, B_130]: (r2_hidden(k4_tarski('#skF_1'(A_129, B_130), '#skF_2'(A_129, B_130)), A_129) | r2_hidden('#skF_3'(A_129, B_130), B_130) | k1_relat_1(A_129)=B_130)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.86/1.66  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.66  tff(c_76, plain, (![A_52, B_53]: (~r2_hidden(A_52, k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.86/1.66  tff(c_79, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_76])).
% 3.86/1.66  tff(c_719, plain, (![B_131]: (r2_hidden('#skF_3'(k1_xboole_0, B_131), B_131) | k1_relat_1(k1_xboole_0)=B_131)), inference(resolution, [status(thm)], [c_635, c_79])).
% 3.86/1.66  tff(c_799, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_719, c_79])).
% 3.86/1.66  tff(c_718, plain, (![B_130]: (r2_hidden('#skF_3'(k1_xboole_0, B_130), B_130) | k1_relat_1(k1_xboole_0)=B_130)), inference(resolution, [status(thm)], [c_635, c_79])).
% 3.86/1.66  tff(c_820, plain, (![B_130]: (r2_hidden('#skF_3'(k1_xboole_0, B_130), B_130) | k1_xboole_0=B_130)), inference(demodulation, [status(thm), theory('equality')], [c_799, c_718])).
% 3.86/1.66  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.66  tff(c_845, plain, (![B_135]: (r2_hidden('#skF_3'(k1_xboole_0, B_135), B_135) | k1_xboole_0=B_135)), inference(demodulation, [status(thm), theory('equality')], [c_799, c_718])).
% 3.86/1.66  tff(c_26, plain, (![A_24, B_25]: (v1_funct_1('#skF_5'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.66  tff(c_24, plain, (![A_24, B_25]: (k1_relat_1('#skF_5'(A_24, B_25))=A_24)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.66  tff(c_28, plain, (![A_24, B_25]: (v1_relat_1('#skF_5'(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.66  tff(c_34, plain, (![A_31]: (v1_funct_1('#skF_6'(A_31)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.86/1.66  tff(c_32, plain, (![A_31]: (k1_relat_1('#skF_6'(A_31))=A_31)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.86/1.66  tff(c_36, plain, (![A_31]: (v1_relat_1('#skF_6'(A_31)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.86/1.66  tff(c_83, plain, (![C_54, B_55]: (C_54=B_55 | k1_relat_1(C_54)!='#skF_7' | k1_relat_1(B_55)!='#skF_7' | ~v1_funct_1(C_54) | ~v1_relat_1(C_54) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.86/1.66  tff(c_87, plain, (![B_55, A_31]: (B_55='#skF_6'(A_31) | k1_relat_1('#skF_6'(A_31))!='#skF_7' | k1_relat_1(B_55)!='#skF_7' | ~v1_funct_1('#skF_6'(A_31)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_36, c_83])).
% 3.86/1.66  tff(c_135, plain, (![B_69, A_70]: (B_69='#skF_6'(A_70) | A_70!='#skF_7' | k1_relat_1(B_69)!='#skF_7' | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_87])).
% 3.86/1.66  tff(c_137, plain, (![A_70, A_24, B_25]: ('#skF_6'(A_70)='#skF_5'(A_24, B_25) | A_70!='#skF_7' | k1_relat_1('#skF_5'(A_24, B_25))!='#skF_7' | ~v1_funct_1('#skF_5'(A_24, B_25)))), inference(resolution, [status(thm)], [c_28, c_135])).
% 3.86/1.66  tff(c_217, plain, (![A_78, A_79, B_80]: ('#skF_6'(A_78)='#skF_5'(A_79, B_80) | A_78!='#skF_7' | A_79!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_137])).
% 3.86/1.66  tff(c_22, plain, (![A_24, B_25, D_30]: (k1_funct_1('#skF_5'(A_24, B_25), D_30)=B_25 | ~r2_hidden(D_30, A_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.86/1.66  tff(c_232, plain, (![A_78, D_30, B_80, A_79]: (k1_funct_1('#skF_6'(A_78), D_30)=B_80 | ~r2_hidden(D_30, A_79) | A_78!='#skF_7' | A_79!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_217, c_22])).
% 3.86/1.66  tff(c_1194, plain, (![A_145, B_146]: (k1_funct_1('#skF_6'(A_145), '#skF_3'(k1_xboole_0, B_146))='#skF_7' | A_145!='#skF_7' | B_146!='#skF_7' | k1_xboole_0=B_146)), inference(resolution, [status(thm)], [c_845, c_232])).
% 3.86/1.66  tff(c_30, plain, (![A_31, C_36]: (k1_funct_1('#skF_6'(A_31), C_36)=k1_xboole_0 | ~r2_hidden(C_36, A_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.86/1.66  tff(c_1197, plain, (![B_146, A_145]: (k1_xboole_0='#skF_7' | ~r2_hidden('#skF_3'(k1_xboole_0, B_146), A_145) | A_145!='#skF_7' | B_146!='#skF_7' | k1_xboole_0=B_146)), inference(superposition, [status(thm), theory('equality')], [c_1194, c_30])).
% 3.86/1.66  tff(c_1356, plain, (![B_980, A_981]: (~r2_hidden('#skF_3'(k1_xboole_0, B_980), A_981) | A_981!='#skF_7' | B_980!='#skF_7' | k1_xboole_0=B_980)), inference(negUnitSimplification, [status(thm)], [c_38, c_1197])).
% 3.86/1.66  tff(c_1380, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_820, c_1356])).
% 3.86/1.66  tff(c_1394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1380, c_38])).
% 3.86/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.66  
% 3.86/1.66  Inference rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Ref     : 1
% 3.86/1.66  #Sup     : 333
% 3.86/1.66  #Fact    : 0
% 3.86/1.66  #Define  : 0
% 3.86/1.66  #Split   : 0
% 3.86/1.66  #Chain   : 0
% 3.86/1.66  #Close   : 0
% 3.86/1.66  
% 3.86/1.66  Ordering : KBO
% 3.86/1.66  
% 3.86/1.66  Simplification rules
% 3.86/1.66  ----------------------
% 3.86/1.66  #Subsume      : 96
% 3.86/1.66  #Demod        : 208
% 3.86/1.66  #Tautology    : 50
% 3.86/1.66  #SimpNegUnit  : 4
% 3.86/1.66  #BackRed      : 22
% 3.86/1.66  
% 3.86/1.66  #Partial instantiations: 516
% 3.86/1.66  #Strategies tried      : 1
% 3.86/1.66  
% 3.86/1.66  Timing (in seconds)
% 3.86/1.66  ----------------------
% 3.86/1.67  Preprocessing        : 0.34
% 3.86/1.67  Parsing              : 0.17
% 3.86/1.67  CNF conversion       : 0.03
% 3.86/1.67  Main loop            : 0.49
% 3.86/1.67  Inferencing          : 0.18
% 3.86/1.67  Reduction            : 0.15
% 3.86/1.67  Demodulation         : 0.11
% 3.86/1.67  BG Simplification    : 0.03
% 3.86/1.67  Subsumption          : 0.10
% 3.86/1.67  Abstraction          : 0.03
% 3.86/1.67  MUC search           : 0.00
% 3.86/1.67  Cooper               : 0.00
% 3.86/1.67  Total                : 0.85
% 3.86/1.67  Index Insertion      : 0.00
% 3.86/1.67  Index Deletion       : 0.00
% 3.86/1.67  Index Matching       : 0.00
% 3.86/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
