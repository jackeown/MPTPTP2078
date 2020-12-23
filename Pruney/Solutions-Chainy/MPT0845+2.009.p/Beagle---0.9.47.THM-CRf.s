%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 102 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_73,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_75,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_63] : v1_relat_1(k6_relat_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_48])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [D_89,A_90,B_91] :
      ( ~ r2_hidden(D_89,'#skF_2'(A_90,B_91))
      | ~ r2_hidden(D_89,B_91)
      | ~ r2_hidden(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_727,plain,(
    ! [A_156,B_157,B_158] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_156,B_157),B_158),B_157)
      | ~ r2_hidden(A_156,B_157)
      | r1_xboole_0('#skF_2'(A_156,B_157),B_158) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_733,plain,(
    ! [A_159,B_160] :
      ( ~ r2_hidden(A_159,B_160)
      | r1_xboole_0('#skF_2'(A_159,B_160),B_160) ) ),
    inference(resolution,[status(thm)],[c_4,c_727])).

tff(c_81,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [B_61] :
      ( ~ r1_xboole_0(B_61,'#skF_7')
      | ~ r2_hidden(B_61,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_89,plain,(
    ! [A_73] :
      ( ~ r1_xboole_0('#skF_2'(A_73,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_81,c_40])).

tff(c_742,plain,(
    ! [A_161] : ~ r2_hidden(A_161,'#skF_7') ),
    inference(resolution,[status(thm)],[c_733,c_89])).

tff(c_783,plain,(
    ! [A_1] : r1_xboole_0(A_1,'#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_742])).

tff(c_322,plain,(
    ! [A_124,B_125,C_126] :
      ( r2_hidden('#skF_4'(A_124,B_125,C_126),B_125)
      | r2_hidden('#skF_5'(A_124,B_125,C_126),C_126)
      | k10_relat_1(A_124,B_125) = C_126
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [B_59,A_58] :
      ( ~ r1_tarski(B_59,A_58)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_98,plain,(
    ! [B_78,A_79] :
      ( ~ r1_tarski(B_78,'#skF_2'(A_79,B_78))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_81,c_38])).

tff(c_103,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_381,plain,(
    ! [A_127,C_128] :
      ( r2_hidden('#skF_5'(A_127,k1_xboole_0,C_128),C_128)
      | k10_relat_1(A_127,k1_xboole_0) = C_128
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_322,c_103])).

tff(c_412,plain,(
    ! [A_127] :
      ( ~ r1_xboole_0('#skF_5'(A_127,k1_xboole_0,'#skF_7'),'#skF_7')
      | k10_relat_1(A_127,k1_xboole_0) = '#skF_7'
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_381,c_40])).

tff(c_844,plain,(
    ! [A_167] :
      ( k10_relat_1(A_167,k1_xboole_0) = '#skF_7'
      | ~ v1_relat_1(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_412])).

tff(c_851,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_50,c_844])).

tff(c_34,plain,(
    ! [A_57] : k10_relat_1(k1_xboole_0,A_57) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_894,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_34])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.71/1.40  
% 2.71/1.40  %Foreground sorts:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Background operators:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Foreground operators:
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.71/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.71/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.40  
% 2.71/1.41  tff(f_92, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.71/1.41  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.71/1.41  tff(f_73, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.71/1.41  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.71/1.41  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.71/1.41  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.71/1.41  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.41  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.71/1.41  tff(f_75, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.71/1.41  tff(c_42, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.41  tff(c_36, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.71/1.41  tff(c_48, plain, (![A_63]: (v1_relat_1(k6_relat_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.41  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_48])).
% 2.71/1.41  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.41  tff(c_138, plain, (![D_89, A_90, B_91]: (~r2_hidden(D_89, '#skF_2'(A_90, B_91)) | ~r2_hidden(D_89, B_91) | ~r2_hidden(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.41  tff(c_727, plain, (![A_156, B_157, B_158]: (~r2_hidden('#skF_1'('#skF_2'(A_156, B_157), B_158), B_157) | ~r2_hidden(A_156, B_157) | r1_xboole_0('#skF_2'(A_156, B_157), B_158))), inference(resolution, [status(thm)], [c_6, c_138])).
% 2.71/1.41  tff(c_733, plain, (![A_159, B_160]: (~r2_hidden(A_159, B_160) | r1_xboole_0('#skF_2'(A_159, B_160), B_160))), inference(resolution, [status(thm)], [c_4, c_727])).
% 2.71/1.41  tff(c_81, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.41  tff(c_40, plain, (![B_61]: (~r1_xboole_0(B_61, '#skF_7') | ~r2_hidden(B_61, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.41  tff(c_89, plain, (![A_73]: (~r1_xboole_0('#skF_2'(A_73, '#skF_7'), '#skF_7') | ~r2_hidden(A_73, '#skF_7'))), inference(resolution, [status(thm)], [c_81, c_40])).
% 2.71/1.41  tff(c_742, plain, (![A_161]: (~r2_hidden(A_161, '#skF_7'))), inference(resolution, [status(thm)], [c_733, c_89])).
% 2.71/1.41  tff(c_783, plain, (![A_1]: (r1_xboole_0(A_1, '#skF_7'))), inference(resolution, [status(thm)], [c_4, c_742])).
% 2.71/1.41  tff(c_322, plain, (![A_124, B_125, C_126]: (r2_hidden('#skF_4'(A_124, B_125, C_126), B_125) | r2_hidden('#skF_5'(A_124, B_125, C_126), C_126) | k10_relat_1(A_124, B_125)=C_126 | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.41  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.41  tff(c_38, plain, (![B_59, A_58]: (~r1_tarski(B_59, A_58) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.41  tff(c_98, plain, (![B_78, A_79]: (~r1_tarski(B_78, '#skF_2'(A_79, B_78)) | ~r2_hidden(A_79, B_78))), inference(resolution, [status(thm)], [c_81, c_38])).
% 2.71/1.41  tff(c_103, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_98])).
% 2.71/1.41  tff(c_381, plain, (![A_127, C_128]: (r2_hidden('#skF_5'(A_127, k1_xboole_0, C_128), C_128) | k10_relat_1(A_127, k1_xboole_0)=C_128 | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_322, c_103])).
% 2.71/1.41  tff(c_412, plain, (![A_127]: (~r1_xboole_0('#skF_5'(A_127, k1_xboole_0, '#skF_7'), '#skF_7') | k10_relat_1(A_127, k1_xboole_0)='#skF_7' | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_381, c_40])).
% 2.71/1.41  tff(c_844, plain, (![A_167]: (k10_relat_1(A_167, k1_xboole_0)='#skF_7' | ~v1_relat_1(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_412])).
% 2.71/1.41  tff(c_851, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_50, c_844])).
% 2.71/1.41  tff(c_34, plain, (![A_57]: (k10_relat_1(k1_xboole_0, A_57)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.71/1.41  tff(c_894, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_851, c_34])).
% 2.71/1.41  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_894])).
% 2.71/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  Inference rules
% 2.71/1.41  ----------------------
% 2.71/1.41  #Ref     : 0
% 2.71/1.41  #Sup     : 177
% 2.71/1.41  #Fact    : 0
% 2.71/1.41  #Define  : 0
% 2.71/1.41  #Split   : 1
% 2.71/1.41  #Chain   : 0
% 2.71/1.41  #Close   : 0
% 2.71/1.41  
% 2.71/1.41  Ordering : KBO
% 2.71/1.41  
% 2.71/1.41  Simplification rules
% 2.71/1.41  ----------------------
% 2.71/1.41  #Subsume      : 54
% 2.71/1.41  #Demod        : 108
% 2.71/1.41  #Tautology    : 33
% 2.71/1.41  #SimpNegUnit  : 5
% 2.71/1.41  #BackRed      : 5
% 2.71/1.41  
% 2.71/1.41  #Partial instantiations: 0
% 2.71/1.41  #Strategies tried      : 1
% 2.71/1.41  
% 2.71/1.41  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.42  Preprocessing        : 0.30
% 2.71/1.42  Parsing              : 0.16
% 2.71/1.42  CNF conversion       : 0.03
% 2.71/1.42  Main loop            : 0.35
% 2.71/1.42  Inferencing          : 0.13
% 2.71/1.42  Reduction            : 0.10
% 2.71/1.42  Demodulation         : 0.07
% 2.71/1.42  BG Simplification    : 0.02
% 2.71/1.42  Subsumption          : 0.08
% 2.71/1.42  Abstraction          : 0.02
% 2.71/1.42  MUC search           : 0.00
% 2.71/1.42  Cooper               : 0.00
% 2.71/1.42  Total                : 0.68
% 2.71/1.42  Index Insertion      : 0.00
% 2.71/1.42  Index Deletion       : 0.00
% 2.71/1.42  Index Matching       : 0.00
% 2.71/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
