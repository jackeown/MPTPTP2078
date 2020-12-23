%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   56 (  65 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   77 ( 102 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_62,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_68,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ! [B_56,A_55] :
      ( ~ r1_tarski(B_56,A_55)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_126,plain,(
    ! [B_82,A_83] :
      ( ~ r1_tarski(B_82,'#skF_2'(A_83,B_82))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_68,c_42])).

tff(c_131,plain,(
    ! [A_83] : ~ r2_hidden(A_83,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [A_54] : v1_relat_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_40,plain,(
    ! [A_54] : v1_funct_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_298,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_4'(A_119,B_120),k1_relat_1(A_119))
      | r2_hidden('#skF_5'(A_119,B_120),B_120)
      | k2_relat_1(A_119) = B_120
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_315,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_120),k1_xboole_0)
      | r2_hidden('#skF_5'(k1_xboole_0,B_120),B_120)
      | k2_relat_1(k1_xboole_0) = B_120
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_298])).

tff(c_320,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_120),k1_xboole_0)
      | r2_hidden('#skF_5'(k1_xboole_0,B_120),B_120)
      | k1_xboole_0 = B_120 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_14,c_315])).

tff(c_322,plain,(
    ! [B_121] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_121),B_121)
      | k1_xboole_0 = B_121 ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_320])).

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

tff(c_160,plain,(
    ! [D_88,A_89,B_90] :
      ( ~ r2_hidden(D_88,'#skF_2'(A_89,B_90))
      | ~ r2_hidden(D_88,B_90)
      | ~ r2_hidden(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_225,plain,(
    ! [A_105,B_106,B_107] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_105,B_106),B_107),B_106)
      | ~ r2_hidden(A_105,B_106)
      | r1_xboole_0('#skF_2'(A_105,B_106),B_107) ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_248,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden(A_110,B_111)
      | r1_xboole_0('#skF_2'(A_110,B_111),B_111) ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_44,plain,(
    ! [B_58] :
      ( ~ r1_xboole_0(B_58,'#skF_7')
      | ~ r2_hidden(B_58,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_77,plain,(
    ! [A_65] :
      ( ~ r1_xboole_0('#skF_2'(A_65,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_65,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_44])).

tff(c_255,plain,(
    ! [A_110] : ~ r2_hidden(A_110,'#skF_7') ),
    inference(resolution,[status(thm)],[c_248,c_77])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_322,c_255])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:16:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.26  
% 2.25/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.25/1.27  
% 2.25/1.27  %Foreground sorts:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Background operators:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Foreground operators:
% 2.25/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.25/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.25/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.25/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.25/1.27  
% 2.25/1.28  tff(f_97, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.25/1.28  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.25/1.28  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 2.25/1.28  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.25/1.28  tff(f_62, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.25/1.28  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.25/1.28  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.25/1.28  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.25/1.28  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.25/1.28  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.25/1.28  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.28  tff(c_68, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.28  tff(c_42, plain, (![B_56, A_55]: (~r1_tarski(B_56, A_55) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.25/1.28  tff(c_126, plain, (![B_82, A_83]: (~r1_tarski(B_82, '#skF_2'(A_83, B_82)) | ~r2_hidden(A_83, B_82))), inference(resolution, [status(thm)], [c_68, c_42])).
% 2.25/1.28  tff(c_131, plain, (![A_83]: (~r2_hidden(A_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_126])).
% 2.25/1.28  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.28  tff(c_38, plain, (![A_54]: (v1_relat_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.28  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_38])).
% 2.25/1.28  tff(c_40, plain, (![A_54]: (v1_funct_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.28  tff(c_62, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_40])).
% 2.25/1.28  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.28  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.28  tff(c_298, plain, (![A_119, B_120]: (r2_hidden('#skF_4'(A_119, B_120), k1_relat_1(A_119)) | r2_hidden('#skF_5'(A_119, B_120), B_120) | k2_relat_1(A_119)=B_120 | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.28  tff(c_315, plain, (![B_120]: (r2_hidden('#skF_4'(k1_xboole_0, B_120), k1_xboole_0) | r2_hidden('#skF_5'(k1_xboole_0, B_120), B_120) | k2_relat_1(k1_xboole_0)=B_120 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_298])).
% 2.25/1.28  tff(c_320, plain, (![B_120]: (r2_hidden('#skF_4'(k1_xboole_0, B_120), k1_xboole_0) | r2_hidden('#skF_5'(k1_xboole_0, B_120), B_120) | k1_xboole_0=B_120)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_14, c_315])).
% 2.25/1.28  tff(c_322, plain, (![B_121]: (r2_hidden('#skF_5'(k1_xboole_0, B_121), B_121) | k1_xboole_0=B_121)), inference(negUnitSimplification, [status(thm)], [c_131, c_320])).
% 2.25/1.28  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.28  tff(c_160, plain, (![D_88, A_89, B_90]: (~r2_hidden(D_88, '#skF_2'(A_89, B_90)) | ~r2_hidden(D_88, B_90) | ~r2_hidden(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.28  tff(c_225, plain, (![A_105, B_106, B_107]: (~r2_hidden('#skF_1'('#skF_2'(A_105, B_106), B_107), B_106) | ~r2_hidden(A_105, B_106) | r1_xboole_0('#skF_2'(A_105, B_106), B_107))), inference(resolution, [status(thm)], [c_6, c_160])).
% 2.25/1.28  tff(c_248, plain, (![A_110, B_111]: (~r2_hidden(A_110, B_111) | r1_xboole_0('#skF_2'(A_110, B_111), B_111))), inference(resolution, [status(thm)], [c_4, c_225])).
% 2.25/1.28  tff(c_44, plain, (![B_58]: (~r1_xboole_0(B_58, '#skF_7') | ~r2_hidden(B_58, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.25/1.28  tff(c_77, plain, (![A_65]: (~r1_xboole_0('#skF_2'(A_65, '#skF_7'), '#skF_7') | ~r2_hidden(A_65, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_44])).
% 2.25/1.28  tff(c_255, plain, (![A_110]: (~r2_hidden(A_110, '#skF_7'))), inference(resolution, [status(thm)], [c_248, c_77])).
% 2.25/1.28  tff(c_326, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_322, c_255])).
% 2.25/1.28  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_326])).
% 2.25/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  Inference rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Ref     : 0
% 2.25/1.28  #Sup     : 59
% 2.25/1.28  #Fact    : 0
% 2.25/1.28  #Define  : 0
% 2.25/1.28  #Split   : 0
% 2.25/1.28  #Chain   : 0
% 2.25/1.28  #Close   : 0
% 2.25/1.28  
% 2.25/1.28  Ordering : KBO
% 2.25/1.28  
% 2.25/1.28  Simplification rules
% 2.25/1.28  ----------------------
% 2.25/1.28  #Subsume      : 19
% 2.25/1.28  #Demod        : 39
% 2.25/1.28  #Tautology    : 15
% 2.25/1.28  #SimpNegUnit  : 5
% 2.25/1.28  #BackRed      : 1
% 2.25/1.28  
% 2.25/1.28  #Partial instantiations: 0
% 2.25/1.28  #Strategies tried      : 1
% 2.25/1.28  
% 2.25/1.28  Timing (in seconds)
% 2.25/1.28  ----------------------
% 2.25/1.28  Preprocessing        : 0.31
% 2.25/1.28  Parsing              : 0.17
% 2.25/1.28  CNF conversion       : 0.03
% 2.25/1.28  Main loop            : 0.20
% 2.25/1.28  Inferencing          : 0.08
% 2.25/1.28  Reduction            : 0.06
% 2.25/1.28  Demodulation         : 0.04
% 2.25/1.28  BG Simplification    : 0.01
% 2.25/1.28  Subsumption          : 0.04
% 2.25/1.28  Abstraction          : 0.01
% 2.25/1.28  MUC search           : 0.00
% 2.25/1.28  Cooper               : 0.00
% 2.25/1.28  Total                : 0.55
% 2.25/1.28  Index Insertion      : 0.00
% 2.25/1.28  Index Deletion       : 0.00
% 2.25/1.28  Index Matching       : 0.00
% 2.25/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
