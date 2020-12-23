%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 167 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 398 expanded)
%              Number of equality atoms :   51 ( 196 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_104,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_42,plain,(
    ! [A_23,B_27] :
      ( k1_relat_1('#skF_4'(A_23,B_27)) = A_23
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    ! [A_23,B_27] :
      ( v1_funct_1('#skF_4'(A_23,B_27))
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    ! [A_23,B_27] :
      ( v1_relat_1('#skF_4'(A_23,B_27))
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_tarski(A_19),B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_99,plain,(
    ! [A_47,B_48] :
      ( k2_relat_1('#skF_4'(A_47,B_48)) = k1_tarski(B_48)
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_48,plain,(
    ! [C_30] :
      ( ~ r1_tarski(k2_relat_1(C_30),'#skF_5')
      | k1_relat_1(C_30) != '#skF_6'
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_111,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(k1_tarski(B_49),'#skF_5')
      | k1_relat_1('#skF_4'(A_50,B_49)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_50,B_49))
      | ~ v1_relat_1('#skF_4'(A_50,B_49))
      | k1_xboole_0 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_48])).

tff(c_147,plain,(
    ! [A_69,A_70] :
      ( k1_relat_1('#skF_4'(A_69,A_70)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_69,A_70))
      | ~ v1_relat_1('#skF_4'(A_69,A_70))
      | k1_xboole_0 = A_69
      | ~ r2_hidden(A_70,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_205,plain,(
    ! [A_99,B_100] :
      ( k1_relat_1('#skF_4'(A_99,B_100)) != '#skF_6'
      | ~ v1_funct_1('#skF_4'(A_99,B_100))
      | ~ r2_hidden(B_100,'#skF_5')
      | k1_xboole_0 = A_99 ) ),
    inference(resolution,[status(thm)],[c_46,c_147])).

tff(c_210,plain,(
    ! [A_101,B_102] :
      ( k1_relat_1('#skF_4'(A_101,B_102)) != '#skF_6'
      | ~ r2_hidden(B_102,'#skF_5')
      | k1_xboole_0 = A_101 ) ),
    inference(resolution,[status(thm)],[c_44,c_205])).

tff(c_213,plain,(
    ! [A_23,B_27] :
      ( A_23 != '#skF_6'
      | ~ r2_hidden(B_27,'#skF_5')
      | k1_xboole_0 = A_23
      | k1_xboole_0 = A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_210])).

tff(c_214,plain,(
    ! [B_27] : ~ r2_hidden(B_27,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_3'(A_16,B_17),A_16)
      | k1_xboole_0 = A_16
      | k1_tarski(B_17) = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_215,plain,(
    ! [B_103] : ~ r2_hidden(B_103,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_241,plain,(
    ! [B_17] :
      ( k1_xboole_0 = '#skF_5'
      | k1_tarski(B_17) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_262,plain,(
    ! [B_17] : k1_tarski(B_17) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_241])).

tff(c_119,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_1'(A_57,B_58),A_57)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_59] : r1_tarski(A_59,A_59) ),
    inference(resolution,[status(thm)],[c_119,c_4])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | ~ r1_tarski(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(resolution,[status(thm)],[c_125,c_28])).

tff(c_302,plain,(
    ! [A_19] : r2_hidden(A_19,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_130])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_302])).

tff(c_311,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_33] :
      ( v1_relat_1(A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_61,plain,(
    ! [A_32] :
      ( v1_funct_1(A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_65,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_61])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ! [C_34] :
      ( ~ r1_tarski(k2_relat_1(C_34),'#skF_5')
      | k1_relat_1(C_34) != '#skF_6'
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_5')
    | k1_relat_1(k1_xboole_0) != '#skF_6'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_76,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36,c_16,c_74])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_76])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_78])).

tff(c_333,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_344,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_8])).

tff(c_369,plain,(
    ! [A_114] :
      ( v1_relat_1(A_114)
      | ~ v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_373,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_344,c_369])).

tff(c_364,plain,(
    ! [A_113] :
      ( v1_funct_1(A_113)
      | ~ v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_368,plain,(
    v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_344,c_364])).

tff(c_343,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_36])).

tff(c_342,plain,(
    ! [A_11] : r1_tarski('#skF_6',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_16])).

tff(c_341,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_333,c_34])).

tff(c_334,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_349,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_334])).

tff(c_374,plain,(
    ! [C_115] :
      ( ~ r1_tarski(k2_relat_1(C_115),'#skF_6')
      | k1_relat_1(C_115) != '#skF_6'
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_48])).

tff(c_377,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k1_relat_1('#skF_6') != '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_374])).

tff(c_379,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_343,c_342,c_377])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:35:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.30  
% 2.63/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.63/1.30  
% 2.63/1.30  %Foreground sorts:
% 2.63/1.30  
% 2.63/1.30  
% 2.63/1.30  %Background operators:
% 2.63/1.30  
% 2.63/1.30  
% 2.63/1.30  %Foreground operators:
% 2.63/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.63/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.63/1.30  
% 2.63/1.32  tff(f_104, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.63/1.32  tff(f_80, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 2.63/1.32  tff(f_122, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.63/1.32  tff(f_76, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.63/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.63/1.32  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.63/1.32  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.63/1.32  tff(f_91, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.63/1.32  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.63/1.32  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.63/1.32  tff(c_42, plain, (![A_23, B_27]: (k1_relat_1('#skF_4'(A_23, B_27))=A_23 | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.63/1.32  tff(c_44, plain, (![A_23, B_27]: (v1_funct_1('#skF_4'(A_23, B_27)) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.63/1.32  tff(c_46, plain, (![A_23, B_27]: (v1_relat_1('#skF_4'(A_23, B_27)) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.63/1.32  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(k1_tarski(A_19), B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.32  tff(c_99, plain, (![A_47, B_48]: (k2_relat_1('#skF_4'(A_47, B_48))=k1_tarski(B_48) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.63/1.32  tff(c_48, plain, (![C_30]: (~r1_tarski(k2_relat_1(C_30), '#skF_5') | k1_relat_1(C_30)!='#skF_6' | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.63/1.32  tff(c_111, plain, (![B_49, A_50]: (~r1_tarski(k1_tarski(B_49), '#skF_5') | k1_relat_1('#skF_4'(A_50, B_49))!='#skF_6' | ~v1_funct_1('#skF_4'(A_50, B_49)) | ~v1_relat_1('#skF_4'(A_50, B_49)) | k1_xboole_0=A_50)), inference(superposition, [status(thm), theory('equality')], [c_99, c_48])).
% 2.63/1.32  tff(c_147, plain, (![A_69, A_70]: (k1_relat_1('#skF_4'(A_69, A_70))!='#skF_6' | ~v1_funct_1('#skF_4'(A_69, A_70)) | ~v1_relat_1('#skF_4'(A_69, A_70)) | k1_xboole_0=A_69 | ~r2_hidden(A_70, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_111])).
% 2.63/1.32  tff(c_205, plain, (![A_99, B_100]: (k1_relat_1('#skF_4'(A_99, B_100))!='#skF_6' | ~v1_funct_1('#skF_4'(A_99, B_100)) | ~r2_hidden(B_100, '#skF_5') | k1_xboole_0=A_99)), inference(resolution, [status(thm)], [c_46, c_147])).
% 2.63/1.32  tff(c_210, plain, (![A_101, B_102]: (k1_relat_1('#skF_4'(A_101, B_102))!='#skF_6' | ~r2_hidden(B_102, '#skF_5') | k1_xboole_0=A_101)), inference(resolution, [status(thm)], [c_44, c_205])).
% 2.63/1.32  tff(c_213, plain, (![A_23, B_27]: (A_23!='#skF_6' | ~r2_hidden(B_27, '#skF_5') | k1_xboole_0=A_23 | k1_xboole_0=A_23)), inference(superposition, [status(thm), theory('equality')], [c_42, c_210])).
% 2.63/1.32  tff(c_214, plain, (![B_27]: (~r2_hidden(B_27, '#skF_5'))), inference(splitLeft, [status(thm)], [c_213])).
% 2.63/1.32  tff(c_50, plain, (k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.63/1.32  tff(c_60, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_50])).
% 2.63/1.32  tff(c_26, plain, (![A_16, B_17]: (r2_hidden('#skF_3'(A_16, B_17), A_16) | k1_xboole_0=A_16 | k1_tarski(B_17)=A_16)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.32  tff(c_215, plain, (![B_103]: (~r2_hidden(B_103, '#skF_5'))), inference(splitLeft, [status(thm)], [c_213])).
% 2.63/1.32  tff(c_241, plain, (![B_17]: (k1_xboole_0='#skF_5' | k1_tarski(B_17)='#skF_5')), inference(resolution, [status(thm)], [c_26, c_215])).
% 2.63/1.32  tff(c_262, plain, (![B_17]: (k1_tarski(B_17)='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_241])).
% 2.63/1.32  tff(c_119, plain, (![A_57, B_58]: (r2_hidden('#skF_1'(A_57, B_58), A_57) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.32  tff(c_125, plain, (![A_59]: (r1_tarski(A_59, A_59))), inference(resolution, [status(thm)], [c_119, c_4])).
% 2.63/1.32  tff(c_28, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | ~r1_tarski(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.63/1.32  tff(c_130, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(resolution, [status(thm)], [c_125, c_28])).
% 2.63/1.32  tff(c_302, plain, (![A_19]: (r2_hidden(A_19, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_130])).
% 2.63/1.32  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_302])).
% 2.63/1.32  tff(c_311, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_213])).
% 2.63/1.32  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.32  tff(c_66, plain, (![A_33]: (v1_relat_1(A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.63/1.32  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_66])).
% 2.63/1.32  tff(c_61, plain, (![A_32]: (v1_funct_1(A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.32  tff(c_65, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_61])).
% 2.63/1.32  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.32  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.63/1.32  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.63/1.32  tff(c_71, plain, (![C_34]: (~r1_tarski(k2_relat_1(C_34), '#skF_5') | k1_relat_1(C_34)!='#skF_6' | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.63/1.32  tff(c_74, plain, (~r1_tarski(k1_xboole_0, '#skF_5') | k1_relat_1(k1_xboole_0)!='#skF_6' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_71])).
% 2.63/1.32  tff(c_76, plain, (k1_xboole_0!='#skF_6' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36, c_16, c_74])).
% 2.63/1.32  tff(c_78, plain, (k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_76])).
% 2.63/1.32  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_311, c_78])).
% 2.63/1.32  tff(c_333, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 2.63/1.32  tff(c_344, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_8])).
% 2.63/1.32  tff(c_369, plain, (![A_114]: (v1_relat_1(A_114) | ~v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.63/1.32  tff(c_373, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_344, c_369])).
% 2.63/1.32  tff(c_364, plain, (![A_113]: (v1_funct_1(A_113) | ~v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.32  tff(c_368, plain, (v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_344, c_364])).
% 2.63/1.32  tff(c_343, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_36])).
% 2.63/1.32  tff(c_342, plain, (![A_11]: (r1_tarski('#skF_6', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_16])).
% 2.63/1.32  tff(c_341, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_333, c_34])).
% 2.63/1.32  tff(c_334, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_50])).
% 2.63/1.32  tff(c_349, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_334])).
% 2.63/1.32  tff(c_374, plain, (![C_115]: (~r1_tarski(k2_relat_1(C_115), '#skF_6') | k1_relat_1(C_115)!='#skF_6' | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_48])).
% 2.63/1.32  tff(c_377, plain, (~r1_tarski('#skF_6', '#skF_6') | k1_relat_1('#skF_6')!='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_341, c_374])).
% 2.63/1.32  tff(c_379, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_343, c_342, c_377])).
% 2.63/1.32  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_379])).
% 2.63/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.32  
% 2.63/1.32  Inference rules
% 2.63/1.32  ----------------------
% 2.63/1.32  #Ref     : 0
% 2.63/1.32  #Sup     : 68
% 2.63/1.32  #Fact    : 0
% 2.63/1.32  #Define  : 0
% 2.63/1.32  #Split   : 2
% 2.63/1.32  #Chain   : 0
% 2.63/1.32  #Close   : 0
% 2.63/1.32  
% 2.63/1.32  Ordering : KBO
% 2.63/1.32  
% 2.63/1.32  Simplification rules
% 2.63/1.32  ----------------------
% 2.63/1.32  #Subsume      : 14
% 2.63/1.32  #Demod        : 48
% 2.63/1.32  #Tautology    : 18
% 2.63/1.32  #SimpNegUnit  : 2
% 2.63/1.32  #BackRed      : 33
% 2.63/1.32  
% 2.63/1.32  #Partial instantiations: 0
% 2.63/1.32  #Strategies tried      : 1
% 2.63/1.32  
% 2.63/1.32  Timing (in seconds)
% 2.63/1.32  ----------------------
% 2.63/1.32  Preprocessing        : 0.30
% 2.63/1.32  Parsing              : 0.16
% 2.63/1.32  CNF conversion       : 0.02
% 2.63/1.32  Main loop            : 0.26
% 2.63/1.32  Inferencing          : 0.09
% 2.63/1.32  Reduction            : 0.07
% 2.63/1.32  Demodulation         : 0.04
% 2.63/1.32  BG Simplification    : 0.02
% 2.63/1.32  Subsumption          : 0.06
% 2.63/1.32  Abstraction          : 0.01
% 2.63/1.32  MUC search           : 0.00
% 2.63/1.32  Cooper               : 0.00
% 2.63/1.32  Total                : 0.60
% 2.63/1.32  Index Insertion      : 0.00
% 2.63/1.32  Index Deletion       : 0.00
% 2.63/1.32  Index Matching       : 0.00
% 2.63/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
