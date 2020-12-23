%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:06 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 168 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 423 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

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

tff(f_82,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_40,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_3'(A_15),A_15)
      | v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    ! [A_36,B_37] :
      ( v3_ordinal1(A_36)
      | ~ r2_hidden(A_36,B_37)
      | ~ v3_ordinal1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_55,plain,(
    ! [A_15] :
      ( v3_ordinal1('#skF_3'(A_15))
      | ~ v3_ordinal1(A_15)
      | v1_ordinal1(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_51])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_ordinal1(B_14,A_13)
      | r1_ordinal1(A_13,B_14)
      | ~ v3_ordinal1(B_14)
      | ~ v3_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_158,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ r1_ordinal1(A_67,B_68)
      | ~ v3_ordinal1(B_68)
      | ~ v3_ordinal1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [A_15] :
      ( ~ r1_tarski('#skF_3'(A_15),A_15)
      | v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_349,plain,(
    ! [B_91] :
      ( v1_ordinal1(B_91)
      | ~ r1_ordinal1('#skF_3'(B_91),B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1('#skF_3'(B_91)) ) ),
    inference(resolution,[status(thm)],[c_158,c_24])).

tff(c_358,plain,(
    ! [A_13] :
      ( v1_ordinal1(A_13)
      | r1_ordinal1(A_13,'#skF_3'(A_13))
      | ~ v3_ordinal1('#skF_3'(A_13))
      | ~ v3_ordinal1(A_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_349])).

tff(c_44,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [A_15] :
      ( ~ r1_tarski(A_15,'#skF_3'(A_15))
      | v1_ordinal1(A_15) ) ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_458,plain,(
    ! [A_104] :
      ( v1_ordinal1(A_104)
      | ~ r1_ordinal1(A_104,'#skF_3'(A_104))
      | ~ v3_ordinal1('#skF_3'(A_104))
      | ~ v3_ordinal1(A_104) ) ),
    inference(resolution,[status(thm)],[c_158,c_48])).

tff(c_467,plain,(
    ! [A_105] :
      ( v1_ordinal1(A_105)
      | ~ v3_ordinal1('#skF_3'(A_105))
      | ~ v3_ordinal1(A_105) ) ),
    inference(resolution,[status(thm)],[c_358,c_458])).

tff(c_472,plain,(
    ! [A_106] :
      ( ~ v3_ordinal1(A_106)
      | v1_ordinal1(A_106) ) ),
    inference(resolution,[status(thm)],[c_55,c_467])).

tff(c_488,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_472])).

tff(c_106,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(k3_tarski(A_55),B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [B_18,A_15] :
      ( r1_tarski(B_18,A_15)
      | ~ r2_hidden(B_18,A_15)
      | ~ v1_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_296,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),A_88)
      | ~ v1_ordinal1(A_88)
      | r1_tarski(k3_tarski(A_88),B_89) ) ),
    inference(resolution,[status(thm)],[c_106,c_22])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski('#skF_2'(A_10,B_11),B_11)
      | r1_tarski(k3_tarski(A_10),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_332,plain,(
    ! [A_90] :
      ( ~ v1_ordinal1(A_90)
      | r1_tarski(k3_tarski(A_90),A_90) ) ),
    inference(resolution,[status(thm)],[c_296,c_16])).

tff(c_119,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_3'(A_64),B_65)
      | ~ r1_tarski(A_64,B_65)
      | v1_ordinal1(A_64) ) ),
    inference(resolution,[status(thm)],[c_26,c_119])).

tff(c_56,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k3_tarski(B_39))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [B_39] :
      ( v1_ordinal1(k3_tarski(B_39))
      | ~ r2_hidden('#skF_3'(k3_tarski(B_39)),B_39) ) ),
    inference(resolution,[status(thm)],[c_56,c_24])).

tff(c_148,plain,(
    ! [B_65] :
      ( ~ r1_tarski(k3_tarski(B_65),B_65)
      | v1_ordinal1(k3_tarski(B_65)) ) ),
    inference(resolution,[status(thm)],[c_131,c_61])).

tff(c_348,plain,(
    ! [A_90] :
      ( v1_ordinal1(k3_tarski(A_90))
      | ~ v1_ordinal1(A_90) ) ),
    inference(resolution,[status(thm)],[c_332,c_148])).

tff(c_328,plain,(
    ! [A_88] :
      ( ~ v1_ordinal1(A_88)
      | r1_tarski(k3_tarski(A_88),A_88) ) ),
    inference(resolution,[status(thm)],[c_296,c_16])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_199,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(A_72,B_73)
      | ~ r2_xboole_0(A_72,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v1_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_491,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,B_111)
      | ~ v3_ordinal1(B_111)
      | ~ v1_ordinal1(A_110)
      | B_111 = A_110
      | ~ r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_8,c_199])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( v3_ordinal1(A_24)
      | ~ r2_hidden(A_24,B_25)
      | ~ v3_ordinal1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_570,plain,(
    ! [A_115,B_116] :
      ( v3_ordinal1(A_115)
      | ~ v3_ordinal1(B_116)
      | ~ v1_ordinal1(A_115)
      | B_116 = A_115
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_491,c_34])).

tff(c_1687,plain,(
    ! [A_201] :
      ( v3_ordinal1(k3_tarski(A_201))
      | ~ v3_ordinal1(A_201)
      | ~ v1_ordinal1(k3_tarski(A_201))
      | k3_tarski(A_201) = A_201
      | ~ v1_ordinal1(A_201) ) ),
    inference(resolution,[status(thm)],[c_328,c_570])).

tff(c_38,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1701,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4'
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1687,c_38])).

tff(c_1709,plain,
    ( ~ v1_ordinal1(k3_tarski('#skF_4'))
    | k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_40,c_1701])).

tff(c_1710,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1709])).

tff(c_1762,plain,(
    ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_348,c_1710])).

tff(c_1769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_1762])).

tff(c_1770,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1709])).

tff(c_1772,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1770,c_38])).

tff(c_1775,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.68  
% 3.69/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.69  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 4.05/1.69  
% 4.05/1.69  %Foreground sorts:
% 4.05/1.69  
% 4.05/1.69  
% 4.05/1.69  %Background operators:
% 4.05/1.69  
% 4.05/1.69  
% 4.05/1.69  %Foreground operators:
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.05/1.69  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 4.05/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.05/1.69  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.05/1.69  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.05/1.69  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.05/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.05/1.69  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.05/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.05/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.05/1.69  
% 4.05/1.70  tff(f_98, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 4.05/1.70  tff(f_65, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.05/1.70  tff(f_88, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 4.05/1.70  tff(f_58, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 4.05/1.70  tff(f_73, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.05/1.70  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.05/1.70  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 4.05/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.05/1.70  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.05/1.70  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.05/1.70  tff(f_82, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 4.05/1.70  tff(c_40, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.05/1.70  tff(c_26, plain, (![A_15]: (r2_hidden('#skF_3'(A_15), A_15) | v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.05/1.70  tff(c_51, plain, (![A_36, B_37]: (v3_ordinal1(A_36) | ~r2_hidden(A_36, B_37) | ~v3_ordinal1(B_37))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.05/1.70  tff(c_55, plain, (![A_15]: (v3_ordinal1('#skF_3'(A_15)) | ~v3_ordinal1(A_15) | v1_ordinal1(A_15))), inference(resolution, [status(thm)], [c_26, c_51])).
% 4.05/1.70  tff(c_20, plain, (![B_14, A_13]: (r1_ordinal1(B_14, A_13) | r1_ordinal1(A_13, B_14) | ~v3_ordinal1(B_14) | ~v3_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.05/1.70  tff(c_158, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~r1_ordinal1(A_67, B_68) | ~v3_ordinal1(B_68) | ~v3_ordinal1(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.05/1.70  tff(c_24, plain, (![A_15]: (~r1_tarski('#skF_3'(A_15), A_15) | v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.05/1.70  tff(c_349, plain, (![B_91]: (v1_ordinal1(B_91) | ~r1_ordinal1('#skF_3'(B_91), B_91) | ~v3_ordinal1(B_91) | ~v3_ordinal1('#skF_3'(B_91)))), inference(resolution, [status(thm)], [c_158, c_24])).
% 4.05/1.70  tff(c_358, plain, (![A_13]: (v1_ordinal1(A_13) | r1_ordinal1(A_13, '#skF_3'(A_13)) | ~v3_ordinal1('#skF_3'(A_13)) | ~v3_ordinal1(A_13))), inference(resolution, [status(thm)], [c_20, c_349])).
% 4.05/1.70  tff(c_44, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.05/1.70  tff(c_48, plain, (![A_15]: (~r1_tarski(A_15, '#skF_3'(A_15)) | v1_ordinal1(A_15))), inference(resolution, [status(thm)], [c_26, c_44])).
% 4.05/1.70  tff(c_458, plain, (![A_104]: (v1_ordinal1(A_104) | ~r1_ordinal1(A_104, '#skF_3'(A_104)) | ~v3_ordinal1('#skF_3'(A_104)) | ~v3_ordinal1(A_104))), inference(resolution, [status(thm)], [c_158, c_48])).
% 4.05/1.70  tff(c_467, plain, (![A_105]: (v1_ordinal1(A_105) | ~v3_ordinal1('#skF_3'(A_105)) | ~v3_ordinal1(A_105))), inference(resolution, [status(thm)], [c_358, c_458])).
% 4.05/1.70  tff(c_472, plain, (![A_106]: (~v3_ordinal1(A_106) | v1_ordinal1(A_106))), inference(resolution, [status(thm)], [c_55, c_467])).
% 4.05/1.70  tff(c_488, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_472])).
% 4.05/1.70  tff(c_106, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(k3_tarski(A_55), B_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/1.70  tff(c_22, plain, (![B_18, A_15]: (r1_tarski(B_18, A_15) | ~r2_hidden(B_18, A_15) | ~v1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.05/1.70  tff(c_296, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), A_88) | ~v1_ordinal1(A_88) | r1_tarski(k3_tarski(A_88), B_89))), inference(resolution, [status(thm)], [c_106, c_22])).
% 4.05/1.70  tff(c_16, plain, (![A_10, B_11]: (~r1_tarski('#skF_2'(A_10, B_11), B_11) | r1_tarski(k3_tarski(A_10), B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.05/1.70  tff(c_332, plain, (![A_90]: (~v1_ordinal1(A_90) | r1_tarski(k3_tarski(A_90), A_90))), inference(resolution, [status(thm)], [c_296, c_16])).
% 4.05/1.70  tff(c_119, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.05/1.70  tff(c_131, plain, (![A_64, B_65]: (r2_hidden('#skF_3'(A_64), B_65) | ~r1_tarski(A_64, B_65) | v1_ordinal1(A_64))), inference(resolution, [status(thm)], [c_26, c_119])).
% 4.05/1.70  tff(c_56, plain, (![A_38, B_39]: (r1_tarski(A_38, k3_tarski(B_39)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.05/1.70  tff(c_61, plain, (![B_39]: (v1_ordinal1(k3_tarski(B_39)) | ~r2_hidden('#skF_3'(k3_tarski(B_39)), B_39))), inference(resolution, [status(thm)], [c_56, c_24])).
% 4.05/1.70  tff(c_148, plain, (![B_65]: (~r1_tarski(k3_tarski(B_65), B_65) | v1_ordinal1(k3_tarski(B_65)))), inference(resolution, [status(thm)], [c_131, c_61])).
% 4.05/1.70  tff(c_348, plain, (![A_90]: (v1_ordinal1(k3_tarski(A_90)) | ~v1_ordinal1(A_90))), inference(resolution, [status(thm)], [c_332, c_148])).
% 4.05/1.70  tff(c_328, plain, (![A_88]: (~v1_ordinal1(A_88) | r1_tarski(k3_tarski(A_88), A_88))), inference(resolution, [status(thm)], [c_296, c_16])).
% 4.05/1.70  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.05/1.70  tff(c_199, plain, (![A_72, B_73]: (r2_hidden(A_72, B_73) | ~r2_xboole_0(A_72, B_73) | ~v3_ordinal1(B_73) | ~v1_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.05/1.70  tff(c_491, plain, (![A_110, B_111]: (r2_hidden(A_110, B_111) | ~v3_ordinal1(B_111) | ~v1_ordinal1(A_110) | B_111=A_110 | ~r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_8, c_199])).
% 4.05/1.70  tff(c_34, plain, (![A_24, B_25]: (v3_ordinal1(A_24) | ~r2_hidden(A_24, B_25) | ~v3_ordinal1(B_25))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.05/1.70  tff(c_570, plain, (![A_115, B_116]: (v3_ordinal1(A_115) | ~v3_ordinal1(B_116) | ~v1_ordinal1(A_115) | B_116=A_115 | ~r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_491, c_34])).
% 4.05/1.70  tff(c_1687, plain, (![A_201]: (v3_ordinal1(k3_tarski(A_201)) | ~v3_ordinal1(A_201) | ~v1_ordinal1(k3_tarski(A_201)) | k3_tarski(A_201)=A_201 | ~v1_ordinal1(A_201))), inference(resolution, [status(thm)], [c_328, c_570])).
% 4.05/1.70  tff(c_38, plain, (~v3_ordinal1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.05/1.70  tff(c_1701, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4' | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1687, c_38])).
% 4.05/1.70  tff(c_1709, plain, (~v1_ordinal1(k3_tarski('#skF_4')) | k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_40, c_1701])).
% 4.05/1.70  tff(c_1710, plain, (~v1_ordinal1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_1709])).
% 4.05/1.70  tff(c_1762, plain, (~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_348, c_1710])).
% 4.05/1.70  tff(c_1769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_488, c_1762])).
% 4.05/1.70  tff(c_1770, plain, (k3_tarski('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1709])).
% 4.05/1.70  tff(c_1772, plain, (~v3_ordinal1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1770, c_38])).
% 4.05/1.70  tff(c_1775, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1772])).
% 4.05/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.05/1.70  
% 4.05/1.70  Inference rules
% 4.05/1.70  ----------------------
% 4.05/1.70  #Ref     : 0
% 4.05/1.70  #Sup     : 386
% 4.05/1.70  #Fact    : 2
% 4.05/1.70  #Define  : 0
% 4.05/1.70  #Split   : 1
% 4.05/1.70  #Chain   : 0
% 4.05/1.70  #Close   : 0
% 4.05/1.70  
% 4.05/1.70  Ordering : KBO
% 4.05/1.70  
% 4.05/1.70  Simplification rules
% 4.05/1.70  ----------------------
% 4.05/1.70  #Subsume      : 60
% 4.05/1.70  #Demod        : 16
% 4.05/1.70  #Tautology    : 13
% 4.05/1.70  #SimpNegUnit  : 0
% 4.05/1.70  #BackRed      : 1
% 4.05/1.70  
% 4.05/1.70  #Partial instantiations: 0
% 4.05/1.70  #Strategies tried      : 1
% 4.05/1.70  
% 4.05/1.70  Timing (in seconds)
% 4.05/1.70  ----------------------
% 4.05/1.70  Preprocessing        : 0.30
% 4.05/1.71  Parsing              : 0.17
% 4.05/1.71  CNF conversion       : 0.02
% 4.05/1.71  Main loop            : 0.63
% 4.05/1.71  Inferencing          : 0.24
% 4.05/1.71  Reduction            : 0.13
% 4.05/1.71  Demodulation         : 0.08
% 4.05/1.71  BG Simplification    : 0.03
% 4.05/1.71  Subsumption          : 0.19
% 4.05/1.71  Abstraction          : 0.03
% 4.05/1.71  MUC search           : 0.00
% 4.05/1.71  Cooper               : 0.00
% 4.05/1.71  Total                : 0.97
% 4.05/1.71  Index Insertion      : 0.00
% 4.05/1.71  Index Deletion       : 0.00
% 4.05/1.71  Index Matching       : 0.00
% 4.05/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
