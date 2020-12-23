%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   50 (  67 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 150 expanded)
%              Number of equality atoms :   50 (  78 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_91,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_72,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_717,plain,(
    ! [A_768,B_769] :
      ( r2_hidden('#skF_1'(A_768,B_769),B_769)
      | r2_hidden('#skF_2'(A_768,B_769),A_768)
      | B_769 = A_768 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_114,plain,(
    ! [B_50,A_51] :
      ( ~ r2_hidden(B_50,A_51)
      | k4_xboole_0(A_51,k1_tarski(B_50)) != A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [B_50] : ~ r2_hidden(B_50,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_742,plain,(
    ! [B_769] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_769),B_769)
      | k1_xboole_0 = B_769 ) ),
    inference(resolution,[status(thm)],[c_717,c_119])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [A_13,B_14] : v1_funct_1('#skF_5'(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    ! [A_13,B_14] : k1_relat_1('#skF_5'(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_13,B_14] : v1_relat_1('#skF_5'(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_20] : v1_funct_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_20] : k1_relat_1('#skF_6'(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [A_20] : v1_relat_1('#skF_6'(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    ! [C_42,B_43] :
      ( C_42 = B_43
      | k1_relat_1(C_42) != '#skF_7'
      | k1_relat_1(B_43) != '#skF_7'
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_83,plain,(
    ! [B_43,A_20] :
      ( B_43 = '#skF_6'(A_20)
      | k1_relat_1('#skF_6'(A_20)) != '#skF_7'
      | k1_relat_1(B_43) != '#skF_7'
      | ~ v1_funct_1('#skF_6'(A_20))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_352,plain,(
    ! [B_473,A_474] :
      ( B_473 = '#skF_6'(A_474)
      | A_474 != '#skF_7'
      | k1_relat_1(B_473) != '#skF_7'
      | ~ v1_funct_1(B_473)
      | ~ v1_relat_1(B_473) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_83])).

tff(c_354,plain,(
    ! [A_474,A_13,B_14] :
      ( '#skF_6'(A_474) = '#skF_5'(A_13,B_14)
      | A_474 != '#skF_7'
      | k1_relat_1('#skF_5'(A_13,B_14)) != '#skF_7'
      | ~ v1_funct_1('#skF_5'(A_13,B_14)) ) ),
    inference(resolution,[status(thm)],[c_36,c_352])).

tff(c_423,plain,(
    ! [A_536,A_537,B_538] :
      ( '#skF_6'(A_536) = '#skF_5'(A_537,B_538)
      | A_536 != '#skF_7'
      | A_537 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_354])).

tff(c_30,plain,(
    ! [A_13,B_14,D_19] :
      ( k1_funct_1('#skF_5'(A_13,B_14),D_19) = B_14
      | ~ r2_hidden(D_19,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_833,plain,(
    ! [A_829,D_830,B_831,A_832] :
      ( k1_funct_1('#skF_6'(A_829),D_830) = B_831
      | ~ r2_hidden(D_830,A_832)
      | A_829 != '#skF_7'
      | A_832 != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_30])).

tff(c_1899,plain,(
    ! [A_1831,B_1832] :
      ( k1_funct_1('#skF_6'(A_1831),'#skF_1'(k1_xboole_0,B_1832)) = '#skF_7'
      | A_1831 != '#skF_7'
      | B_1832 != '#skF_7'
      | k1_xboole_0 = B_1832 ) ),
    inference(resolution,[status(thm)],[c_742,c_833])).

tff(c_38,plain,(
    ! [A_20,C_25] :
      ( k1_funct_1('#skF_6'(A_20),C_25) = k1_xboole_0
      | ~ r2_hidden(C_25,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1902,plain,(
    ! [B_1832,A_1831] :
      ( k1_xboole_0 = '#skF_7'
      | ~ r2_hidden('#skF_1'(k1_xboole_0,B_1832),A_1831)
      | A_1831 != '#skF_7'
      | B_1832 != '#skF_7'
      | k1_xboole_0 = B_1832 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1899,c_38])).

tff(c_2150,plain,(
    ! [B_2767,A_2768] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_2767),A_2768)
      | A_2768 != '#skF_7'
      | B_2767 != '#skF_7'
      | k1_xboole_0 = B_2767 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1902])).

tff(c_2178,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_742,c_2150])).

tff(c_2192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2178,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.78  
% 3.97/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.78  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 3.97/1.78  
% 3.97/1.78  %Foreground sorts:
% 3.97/1.78  
% 3.97/1.78  
% 3.97/1.78  %Background operators:
% 3.97/1.78  
% 3.97/1.78  
% 3.97/1.78  %Foreground operators:
% 3.97/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.97/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.78  tff('#skF_7', type, '#skF_7': $i).
% 3.97/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.97/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.97/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.97/1.78  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.97/1.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.97/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.79  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.97/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.97/1.79  
% 4.03/1.80  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 4.03/1.80  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.03/1.80  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.03/1.80  tff(f_91, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 4.03/1.80  tff(f_60, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 4.03/1.80  tff(f_72, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 4.03/1.80  tff(c_717, plain, (![A_768, B_769]: (r2_hidden('#skF_1'(A_768, B_769), B_769) | r2_hidden('#skF_2'(A_768, B_769), A_768) | B_769=A_768)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.03/1.80  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.03/1.80  tff(c_114, plain, (![B_50, A_51]: (~r2_hidden(B_50, A_51) | k4_xboole_0(A_51, k1_tarski(B_50))!=A_51)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.03/1.80  tff(c_119, plain, (![B_50]: (~r2_hidden(B_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_114])).
% 4.03/1.80  tff(c_742, plain, (![B_769]: (r2_hidden('#skF_1'(k1_xboole_0, B_769), B_769) | k1_xboole_0=B_769)), inference(resolution, [status(thm)], [c_717, c_119])).
% 4.03/1.80  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.03/1.80  tff(c_34, plain, (![A_13, B_14]: (v1_funct_1('#skF_5'(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.03/1.80  tff(c_32, plain, (![A_13, B_14]: (k1_relat_1('#skF_5'(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.03/1.80  tff(c_36, plain, (![A_13, B_14]: (v1_relat_1('#skF_5'(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.03/1.80  tff(c_42, plain, (![A_20]: (v1_funct_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.80  tff(c_40, plain, (![A_20]: (k1_relat_1('#skF_6'(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.80  tff(c_44, plain, (![A_20]: (v1_relat_1('#skF_6'(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.80  tff(c_79, plain, (![C_42, B_43]: (C_42=B_43 | k1_relat_1(C_42)!='#skF_7' | k1_relat_1(B_43)!='#skF_7' | ~v1_funct_1(C_42) | ~v1_relat_1(C_42) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.03/1.80  tff(c_83, plain, (![B_43, A_20]: (B_43='#skF_6'(A_20) | k1_relat_1('#skF_6'(A_20))!='#skF_7' | k1_relat_1(B_43)!='#skF_7' | ~v1_funct_1('#skF_6'(A_20)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_44, c_79])).
% 4.03/1.80  tff(c_352, plain, (![B_473, A_474]: (B_473='#skF_6'(A_474) | A_474!='#skF_7' | k1_relat_1(B_473)!='#skF_7' | ~v1_funct_1(B_473) | ~v1_relat_1(B_473))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_83])).
% 4.03/1.80  tff(c_354, plain, (![A_474, A_13, B_14]: ('#skF_6'(A_474)='#skF_5'(A_13, B_14) | A_474!='#skF_7' | k1_relat_1('#skF_5'(A_13, B_14))!='#skF_7' | ~v1_funct_1('#skF_5'(A_13, B_14)))), inference(resolution, [status(thm)], [c_36, c_352])).
% 4.03/1.80  tff(c_423, plain, (![A_536, A_537, B_538]: ('#skF_6'(A_536)='#skF_5'(A_537, B_538) | A_536!='#skF_7' | A_537!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_354])).
% 4.03/1.80  tff(c_30, plain, (![A_13, B_14, D_19]: (k1_funct_1('#skF_5'(A_13, B_14), D_19)=B_14 | ~r2_hidden(D_19, A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.03/1.80  tff(c_833, plain, (![A_829, D_830, B_831, A_832]: (k1_funct_1('#skF_6'(A_829), D_830)=B_831 | ~r2_hidden(D_830, A_832) | A_829!='#skF_7' | A_832!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_423, c_30])).
% 4.03/1.80  tff(c_1899, plain, (![A_1831, B_1832]: (k1_funct_1('#skF_6'(A_1831), '#skF_1'(k1_xboole_0, B_1832))='#skF_7' | A_1831!='#skF_7' | B_1832!='#skF_7' | k1_xboole_0=B_1832)), inference(resolution, [status(thm)], [c_742, c_833])).
% 4.03/1.80  tff(c_38, plain, (![A_20, C_25]: (k1_funct_1('#skF_6'(A_20), C_25)=k1_xboole_0 | ~r2_hidden(C_25, A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.03/1.80  tff(c_1902, plain, (![B_1832, A_1831]: (k1_xboole_0='#skF_7' | ~r2_hidden('#skF_1'(k1_xboole_0, B_1832), A_1831) | A_1831!='#skF_7' | B_1832!='#skF_7' | k1_xboole_0=B_1832)), inference(superposition, [status(thm), theory('equality')], [c_1899, c_38])).
% 4.03/1.80  tff(c_2150, plain, (![B_2767, A_2768]: (~r2_hidden('#skF_1'(k1_xboole_0, B_2767), A_2768) | A_2768!='#skF_7' | B_2767!='#skF_7' | k1_xboole_0=B_2767)), inference(negUnitSimplification, [status(thm)], [c_46, c_1902])).
% 4.03/1.80  tff(c_2178, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_742, c_2150])).
% 4.03/1.80  tff(c_2192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2178, c_46])).
% 4.03/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.80  
% 4.03/1.80  Inference rules
% 4.03/1.80  ----------------------
% 4.03/1.80  #Ref     : 1
% 4.03/1.80  #Sup     : 415
% 4.03/1.80  #Fact    : 0
% 4.03/1.80  #Define  : 0
% 4.03/1.80  #Split   : 0
% 4.03/1.80  #Chain   : 0
% 4.03/1.80  #Close   : 0
% 4.03/1.80  
% 4.03/1.80  Ordering : KBO
% 4.03/1.80  
% 4.03/1.80  Simplification rules
% 4.03/1.80  ----------------------
% 4.03/1.80  #Subsume      : 139
% 4.03/1.80  #Demod        : 63
% 4.03/1.80  #Tautology    : 80
% 4.03/1.80  #SimpNegUnit  : 15
% 4.03/1.80  #BackRed      : 8
% 4.03/1.80  
% 4.03/1.80  #Partial instantiations: 1807
% 4.03/1.80  #Strategies tried      : 1
% 4.03/1.80  
% 4.03/1.80  Timing (in seconds)
% 4.03/1.80  ----------------------
% 4.03/1.80  Preprocessing        : 0.35
% 4.03/1.80  Parsing              : 0.17
% 4.03/1.80  CNF conversion       : 0.03
% 4.03/1.80  Main loop            : 0.55
% 4.03/1.80  Inferencing          : 0.25
% 4.03/1.80  Reduction            : 0.14
% 4.03/1.80  Demodulation         : 0.09
% 4.03/1.80  BG Simplification    : 0.03
% 4.03/1.80  Subsumption          : 0.10
% 4.03/1.80  Abstraction          : 0.03
% 4.03/1.80  MUC search           : 0.00
% 4.03/1.80  Cooper               : 0.00
% 4.03/1.80  Total                : 0.92
% 4.03/1.80  Index Insertion      : 0.00
% 4.03/1.80  Index Deletion       : 0.00
% 4.03/1.80  Index Matching       : 0.00
% 4.03/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
