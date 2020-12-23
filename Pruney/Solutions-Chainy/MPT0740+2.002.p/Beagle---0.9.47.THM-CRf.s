%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 105 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 225 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_36,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [A_24] :
      ( v1_ordinal1(A_24)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_38])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),A_44)
      | r1_tarski(k3_tarski(A_44),B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_17,A_14] :
      ( r1_tarski(B_17,A_14)
      | ~ r2_hidden(B_17,A_14)
      | ~ v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197,plain,(
    ! [A_74,B_75] :
      ( r1_tarski('#skF_2'(A_74,B_75),A_74)
      | ~ v1_ordinal1(A_74)
      | r1_tarski(k3_tarski(A_74),B_75) ) ),
    inference(resolution,[status(thm)],[c_95,c_24])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski('#skF_2'(A_10,B_11),B_11)
      | r1_tarski(k3_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_213,plain,(
    ! [A_76] :
      ( ~ v1_ordinal1(A_76)
      | r1_tarski(k3_tarski(A_76),A_76) ) ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_3'(A_51),B_52)
      | ~ r1_tarski(A_51,B_52)
      | v1_ordinal1(A_51) ) ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_51,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,k3_tarski(B_31))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_14] :
      ( ~ r1_tarski('#skF_3'(A_14),A_14)
      | v1_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [B_31] :
      ( v1_ordinal1(k3_tarski(B_31))
      | ~ r2_hidden('#skF_3'(k3_tarski(B_31)),B_31) ) ),
    inference(resolution,[status(thm)],[c_51,c_26])).

tff(c_133,plain,(
    ! [B_52] :
      ( ~ r1_tarski(k3_tarski(B_52),B_52)
      | v1_ordinal1(k3_tarski(B_52)) ) ),
    inference(resolution,[status(thm)],[c_119,c_56])).

tff(c_220,plain,(
    ! [A_76] :
      ( v1_ordinal1(k3_tarski(A_76))
      | ~ v1_ordinal1(A_76) ) ),
    inference(resolution,[status(thm)],[c_213,c_133])).

tff(c_210,plain,(
    ! [A_74] :
      ( ~ v1_ordinal1(A_74)
      | r1_tarski(k3_tarski(A_74),A_74) ) ),
    inference(resolution,[status(thm)],[c_197,c_16])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | ~ r2_xboole_0(A_58,B_59)
      | ~ v3_ordinal1(B_59)
      | ~ v1_ordinal1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_277,plain,(
    ! [A_90,B_91] :
      ( r2_hidden(A_90,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v1_ordinal1(A_90)
      | B_91 = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( v3_ordinal1(A_21)
      | ~ r2_hidden(A_21,B_22)
      | ~ v3_ordinal1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_387,plain,(
    ! [A_101,B_102] :
      ( v3_ordinal1(A_101)
      | ~ v3_ordinal1(B_102)
      | ~ v1_ordinal1(A_101)
      | B_102 = A_101
      | ~ r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_277,c_32])).

tff(c_695,plain,(
    ! [A_141] :
      ( v3_ordinal1(k3_tarski(A_141))
      | ~ v3_ordinal1(A_141)
      | ~ v1_ordinal1(k3_tarski(A_141))
      | k3_tarski(A_141) = A_141
      | ~ v1_ordinal1(A_141) ) ),
    inference(resolution,[status(thm)],[c_210,c_387])).

tff(c_34,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_710,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4'
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_695,c_34])).

tff(c_718,plain,
    ( ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_710])).

tff(c_719,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_722,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_719])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_722])).

tff(c_730,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_732,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_34])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.50  
% 2.83/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.50  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.83/1.50  
% 2.83/1.50  %Foreground sorts:
% 2.83/1.50  
% 2.83/1.50  
% 2.83/1.50  %Background operators:
% 2.83/1.50  
% 2.83/1.50  
% 2.83/1.50  %Foreground operators:
% 2.83/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.50  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.83/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.50  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.83/1.50  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.83/1.50  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.83/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.83/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.50  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.83/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.50  
% 2.83/1.52  tff(f_83, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 2.83/1.52  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.83/1.52  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.83/1.52  tff(f_63, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.83/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.83/1.52  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.83/1.52  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.83/1.52  tff(f_72, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.83/1.52  tff(f_78, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.83/1.52  tff(c_36, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.52  tff(c_38, plain, (![A_24]: (v1_ordinal1(A_24) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.83/1.52  tff(c_42, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_38])).
% 2.83/1.52  tff(c_95, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), A_44) | r1_tarski(k3_tarski(A_44), B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.52  tff(c_24, plain, (![B_17, A_14]: (r1_tarski(B_17, A_14) | ~r2_hidden(B_17, A_14) | ~v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.52  tff(c_197, plain, (![A_74, B_75]: (r1_tarski('#skF_2'(A_74, B_75), A_74) | ~v1_ordinal1(A_74) | r1_tarski(k3_tarski(A_74), B_75))), inference(resolution, [status(thm)], [c_95, c_24])).
% 2.83/1.52  tff(c_16, plain, (![A_10, B_11]: (~r1_tarski('#skF_2'(A_10, B_11), B_11) | r1_tarski(k3_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.52  tff(c_213, plain, (![A_76]: (~v1_ordinal1(A_76) | r1_tarski(k3_tarski(A_76), A_76))), inference(resolution, [status(thm)], [c_197, c_16])).
% 2.83/1.52  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.52  tff(c_104, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.52  tff(c_119, plain, (![A_51, B_52]: (r2_hidden('#skF_3'(A_51), B_52) | ~r1_tarski(A_51, B_52) | v1_ordinal1(A_51))), inference(resolution, [status(thm)], [c_28, c_104])).
% 2.83/1.52  tff(c_51, plain, (![A_30, B_31]: (r1_tarski(A_30, k3_tarski(B_31)) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.52  tff(c_26, plain, (![A_14]: (~r1_tarski('#skF_3'(A_14), A_14) | v1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.52  tff(c_56, plain, (![B_31]: (v1_ordinal1(k3_tarski(B_31)) | ~r2_hidden('#skF_3'(k3_tarski(B_31)), B_31))), inference(resolution, [status(thm)], [c_51, c_26])).
% 2.83/1.52  tff(c_133, plain, (![B_52]: (~r1_tarski(k3_tarski(B_52), B_52) | v1_ordinal1(k3_tarski(B_52)))), inference(resolution, [status(thm)], [c_119, c_56])).
% 2.83/1.52  tff(c_220, plain, (![A_76]: (v1_ordinal1(k3_tarski(A_76)) | ~v1_ordinal1(A_76))), inference(resolution, [status(thm)], [c_213, c_133])).
% 2.83/1.52  tff(c_210, plain, (![A_74]: (~v1_ordinal1(A_74) | r1_tarski(k3_tarski(A_74), A_74))), inference(resolution, [status(thm)], [c_197, c_16])).
% 2.83/1.52  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.52  tff(c_152, plain, (![A_58, B_59]: (r2_hidden(A_58, B_59) | ~r2_xboole_0(A_58, B_59) | ~v3_ordinal1(B_59) | ~v1_ordinal1(A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.52  tff(c_277, plain, (![A_90, B_91]: (r2_hidden(A_90, B_91) | ~v3_ordinal1(B_91) | ~v1_ordinal1(A_90) | B_91=A_90 | ~r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_8, c_152])).
% 2.83/1.52  tff(c_32, plain, (![A_21, B_22]: (v3_ordinal1(A_21) | ~r2_hidden(A_21, B_22) | ~v3_ordinal1(B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.52  tff(c_387, plain, (![A_101, B_102]: (v3_ordinal1(A_101) | ~v3_ordinal1(B_102) | ~v1_ordinal1(A_101) | B_102=A_101 | ~r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_277, c_32])).
% 2.83/1.52  tff(c_695, plain, (![A_141]: (v3_ordinal1(k3_tarski(A_141)) | ~v3_ordinal1(A_141) | ~v1_ordinal1(k3_tarski(A_141)) | k3_tarski(A_141)=A_141 | ~v1_ordinal1(A_141))), inference(resolution, [status(thm)], [c_210, c_387])).
% 2.83/1.52  tff(c_34, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.83/1.52  tff(c_710, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4' | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_695, c_34])).
% 2.83/1.52  tff(c_718, plain, (~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_710])).
% 2.83/1.52  tff(c_719, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_718])).
% 2.83/1.52  tff(c_722, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_220, c_719])).
% 2.83/1.52  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_722])).
% 2.83/1.52  tff(c_730, plain, (k3_tarski('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_718])).
% 2.83/1.52  tff(c_732, plain, (~v3_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_34])).
% 2.83/1.52  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_732])).
% 2.83/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.52  
% 2.83/1.52  Inference rules
% 2.83/1.52  ----------------------
% 2.83/1.52  #Ref     : 0
% 2.83/1.52  #Sup     : 165
% 2.83/1.52  #Fact    : 0
% 2.83/1.52  #Define  : 0
% 2.83/1.52  #Split   : 1
% 2.83/1.52  #Chain   : 0
% 2.83/1.52  #Close   : 0
% 2.83/1.52  
% 2.83/1.52  Ordering : KBO
% 2.83/1.52  
% 2.83/1.52  Simplification rules
% 2.83/1.52  ----------------------
% 2.83/1.52  #Subsume      : 24
% 2.83/1.52  #Demod        : 8
% 2.83/1.52  #Tautology    : 10
% 2.83/1.52  #SimpNegUnit  : 0
% 2.83/1.52  #BackRed      : 1
% 2.83/1.52  
% 2.83/1.52  #Partial instantiations: 0
% 2.83/1.52  #Strategies tried      : 1
% 2.83/1.52  
% 2.83/1.52  Timing (in seconds)
% 2.83/1.52  ----------------------
% 2.83/1.52  Preprocessing        : 0.29
% 2.83/1.52  Parsing              : 0.17
% 2.83/1.52  CNF conversion       : 0.02
% 2.83/1.52  Main loop            : 0.42
% 2.83/1.52  Inferencing          : 0.17
% 2.83/1.52  Reduction            : 0.09
% 2.83/1.52  Demodulation         : 0.06
% 2.83/1.52  BG Simplification    : 0.02
% 2.83/1.52  Subsumption          : 0.11
% 2.83/1.52  Abstraction          : 0.02
% 2.83/1.52  MUC search           : 0.00
% 2.83/1.52  Cooper               : 0.00
% 2.83/1.52  Total                : 0.73
% 2.83/1.52  Index Insertion      : 0.00
% 2.83/1.52  Index Deletion       : 0.00
% 2.83/1.52  Index Matching       : 0.00
% 2.83/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
