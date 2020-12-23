%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:07 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 135 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 311 expanded)
%              Number of equality atoms :   46 ( 158 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_8,B_12] :
      ( k1_relat_1('#skF_2'(A_8,B_12)) = A_8
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_8,B_12] :
      ( v1_funct_1('#skF_2'(A_8,B_12))
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_8,B_12] :
      ( v1_relat_1('#skF_2'(A_8,B_12))
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_31,B_32] :
      ( k2_relat_1('#skF_2'(A_31,B_32)) = k1_tarski(B_32)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [C_15] :
      ( ~ r1_tarski(k2_relat_1(C_15),'#skF_3')
      | k1_relat_1(C_15) != '#skF_4'
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_91,plain,(
    ! [B_33,A_34] :
      ( ~ r1_tarski(k1_tarski(B_33),'#skF_3')
      | k1_relat_1('#skF_2'(A_34,B_33)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_34,B_33))
      | ~ v1_relat_1('#skF_2'(A_34,B_33))
      | k1_xboole_0 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_96,plain,(
    ! [A_35,A_36] :
      ( k1_relat_1('#skF_2'(A_35,A_36)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_35,A_36))
      | ~ v1_relat_1('#skF_2'(A_35,A_36))
      | k1_xboole_0 = A_35
      | ~ r2_hidden(A_36,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_101,plain,(
    ! [A_37,B_38] :
      ( k1_relat_1('#skF_2'(A_37,B_38)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_37,B_38))
      | ~ r2_hidden(B_38,'#skF_3')
      | k1_xboole_0 = A_37 ) ),
    inference(resolution,[status(thm)],[c_26,c_96])).

tff(c_106,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1('#skF_2'(A_39,B_40)) != '#skF_4'
      | ~ r2_hidden(B_40,'#skF_3')
      | k1_xboole_0 = A_39 ) ),
    inference(resolution,[status(thm)],[c_24,c_101])).

tff(c_109,plain,(
    ! [A_8,B_12] :
      ( A_8 != '#skF_4'
      | ~ r2_hidden(B_12,'#skF_3')
      | k1_xboole_0 = A_8
      | k1_xboole_0 = A_8 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_106])).

tff(c_111,plain,(
    ! [B_41] : ~ r2_hidden(B_41,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_115])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_41,plain,(
    ! [A_17] :
      ( v1_funct_1(A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    ! [C_19] :
      ( ~ r1_tarski(k2_relat_1(C_19),'#skF_3')
      | k1_relat_1(C_19) != '#skF_4'
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_54,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_3')
    | k1_relat_1(k1_xboole_0) != '#skF_4'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_51])).

tff(c_56,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_16,c_6,c_54])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_58])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_144,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_2])).

tff(c_168,plain,(
    ! [A_44] :
      ( v1_relat_1(A_44)
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_168])).

tff(c_173,plain,(
    ! [A_45] :
      ( v1_funct_1(A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,(
    v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_173])).

tff(c_142,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_16])).

tff(c_141,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_6])).

tff(c_143,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_139,c_14])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_149,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_140])).

tff(c_154,plain,(
    ! [C_15] :
      ( ~ r1_tarski(k2_relat_1(C_15),'#skF_4')
      | k1_relat_1(C_15) != '#skF_4'
      | ~ v1_funct_1(C_15)
      | ~ v1_relat_1(C_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_28])).

tff(c_159,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_154])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_177,c_142,c_141,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:08:26 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.09/1.28  
% 2.09/1.28  %Foreground sorts:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Background operators:
% 2.09/1.28  
% 2.09/1.28  
% 2.09/1.28  %Foreground operators:
% 2.09/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.09/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.28  
% 2.09/1.30  tff(f_82, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.09/1.30  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.09/1.30  tff(f_64, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.09/1.30  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.09/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.30  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.09/1.30  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.09/1.30  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.09/1.30  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.09/1.30  tff(c_30, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.09/1.30  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.09/1.30  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.30  tff(c_22, plain, (![A_8, B_12]: (k1_relat_1('#skF_2'(A_8, B_12))=A_8 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.30  tff(c_24, plain, (![A_8, B_12]: (v1_funct_1('#skF_2'(A_8, B_12)) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.30  tff(c_26, plain, (![A_8, B_12]: (v1_relat_1('#skF_2'(A_8, B_12)) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.30  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.30  tff(c_79, plain, (![A_31, B_32]: (k2_relat_1('#skF_2'(A_31, B_32))=k1_tarski(B_32) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.30  tff(c_28, plain, (![C_15]: (~r1_tarski(k2_relat_1(C_15), '#skF_3') | k1_relat_1(C_15)!='#skF_4' | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.09/1.30  tff(c_91, plain, (![B_33, A_34]: (~r1_tarski(k1_tarski(B_33), '#skF_3') | k1_relat_1('#skF_2'(A_34, B_33))!='#skF_4' | ~v1_funct_1('#skF_2'(A_34, B_33)) | ~v1_relat_1('#skF_2'(A_34, B_33)) | k1_xboole_0=A_34)), inference(superposition, [status(thm), theory('equality')], [c_79, c_28])).
% 2.09/1.30  tff(c_96, plain, (![A_35, A_36]: (k1_relat_1('#skF_2'(A_35, A_36))!='#skF_4' | ~v1_funct_1('#skF_2'(A_35, A_36)) | ~v1_relat_1('#skF_2'(A_35, A_36)) | k1_xboole_0=A_35 | ~r2_hidden(A_36, '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_91])).
% 2.09/1.30  tff(c_101, plain, (![A_37, B_38]: (k1_relat_1('#skF_2'(A_37, B_38))!='#skF_4' | ~v1_funct_1('#skF_2'(A_37, B_38)) | ~r2_hidden(B_38, '#skF_3') | k1_xboole_0=A_37)), inference(resolution, [status(thm)], [c_26, c_96])).
% 2.09/1.30  tff(c_106, plain, (![A_39, B_40]: (k1_relat_1('#skF_2'(A_39, B_40))!='#skF_4' | ~r2_hidden(B_40, '#skF_3') | k1_xboole_0=A_39)), inference(resolution, [status(thm)], [c_24, c_101])).
% 2.09/1.30  tff(c_109, plain, (![A_8, B_12]: (A_8!='#skF_4' | ~r2_hidden(B_12, '#skF_3') | k1_xboole_0=A_8 | k1_xboole_0=A_8)), inference(superposition, [status(thm), theory('equality')], [c_22, c_106])).
% 2.09/1.30  tff(c_111, plain, (![B_41]: (~r2_hidden(B_41, '#skF_3'))), inference(splitLeft, [status(thm)], [c_109])).
% 2.09/1.30  tff(c_115, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.09/1.30  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_115])).
% 2.09/1.30  tff(c_121, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_109])).
% 2.09/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.09/1.30  tff(c_46, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.30  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_46])).
% 2.09/1.30  tff(c_41, plain, (![A_17]: (v1_funct_1(A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.30  tff(c_45, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_41])).
% 2.09/1.30  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.30  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.09/1.30  tff(c_14, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.30  tff(c_51, plain, (![C_19]: (~r1_tarski(k2_relat_1(C_19), '#skF_3') | k1_relat_1(C_19)!='#skF_4' | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.09/1.30  tff(c_54, plain, (~r1_tarski(k1_xboole_0, '#skF_3') | k1_relat_1(k1_xboole_0)!='#skF_4' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_51])).
% 2.09/1.30  tff(c_56, plain, (k1_xboole_0!='#skF_4' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_16, c_6, c_54])).
% 2.09/1.30  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56])).
% 2.09/1.30  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_58])).
% 2.09/1.30  tff(c_139, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.30  tff(c_144, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_2])).
% 2.09/1.30  tff(c_168, plain, (![A_44]: (v1_relat_1(A_44) | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.30  tff(c_172, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_168])).
% 2.09/1.30  tff(c_173, plain, (![A_45]: (v1_funct_1(A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.30  tff(c_177, plain, (v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_173])).
% 2.09/1.30  tff(c_142, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_16])).
% 2.09/1.30  tff(c_141, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_6])).
% 2.09/1.30  tff(c_143, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_139, c_14])).
% 2.09/1.30  tff(c_140, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.09/1.30  tff(c_149, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_140])).
% 2.09/1.30  tff(c_154, plain, (![C_15]: (~r1_tarski(k2_relat_1(C_15), '#skF_4') | k1_relat_1(C_15)!='#skF_4' | ~v1_funct_1(C_15) | ~v1_relat_1(C_15))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_28])).
% 2.09/1.30  tff(c_159, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_143, c_154])).
% 2.09/1.30  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_177, c_142, c_141, c_159])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 29
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 2
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Subsume      : 3
% 2.09/1.30  #Demod        : 35
% 2.09/1.30  #Tautology    : 17
% 2.09/1.30  #SimpNegUnit  : 1
% 2.09/1.30  #BackRed      : 19
% 2.09/1.30  
% 2.09/1.30  #Partial instantiations: 0
% 2.09/1.30  #Strategies tried      : 1
% 2.09/1.30  
% 2.09/1.30  Timing (in seconds)
% 2.09/1.30  ----------------------
% 2.09/1.30  Preprocessing        : 0.32
% 2.09/1.30  Parsing              : 0.17
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.18
% 2.09/1.30  Inferencing          : 0.07
% 2.09/1.30  Reduction            : 0.05
% 2.09/1.30  Demodulation         : 0.03
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.03
% 2.09/1.30  Abstraction          : 0.01
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.53
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
