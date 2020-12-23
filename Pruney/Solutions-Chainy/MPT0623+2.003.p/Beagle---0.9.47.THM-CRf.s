%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:06 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 317 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_11,B_15] :
      ( k1_relat_1('#skF_2'(A_11,B_15)) = A_11
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_11,B_15] :
      ( v1_funct_1('#skF_2'(A_11,B_15))
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_11,B_15] :
      ( v1_relat_1('#skF_2'(A_11,B_15))
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [A_37,B_38] :
      ( k2_relat_1('#skF_2'(A_37,B_38)) = k1_tarski(B_38)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [C_18] :
      ( ~ r1_tarski(k2_relat_1(C_18),'#skF_3')
      | k1_relat_1(C_18) != '#skF_4'
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_106,plain,(
    ! [B_39,A_40] :
      ( ~ r1_tarski(k1_tarski(B_39),'#skF_3')
      | k1_relat_1('#skF_2'(A_40,B_39)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_40,B_39))
      | ~ v1_relat_1('#skF_2'(A_40,B_39))
      | k1_xboole_0 = A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_32])).

tff(c_111,plain,(
    ! [A_41,A_42] :
      ( k1_relat_1('#skF_2'(A_41,A_42)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_41,A_42))
      | ~ v1_relat_1('#skF_2'(A_41,A_42))
      | k1_xboole_0 = A_41
      | ~ r2_hidden(A_42,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_116,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1('#skF_2'(A_43,B_44)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_43,B_44))
      | ~ r2_hidden(B_44,'#skF_3')
      | k1_xboole_0 = A_43 ) ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_121,plain,(
    ! [A_45,B_46] :
      ( k1_relat_1('#skF_2'(A_45,B_46)) != '#skF_4'
      | ~ r2_hidden(B_46,'#skF_3')
      | k1_xboole_0 = A_45 ) ),
    inference(resolution,[status(thm)],[c_28,c_116])).

tff(c_124,plain,(
    ! [A_11,B_15] :
      ( A_11 != '#skF_4'
      | ~ r2_hidden(B_15,'#skF_3')
      | k1_xboole_0 = A_11
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_121])).

tff(c_126,plain,(
    ! [B_47] : ~ r2_hidden(B_47,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_131,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_140])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_23] :
      ( v1_relat_1(A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_51,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_55,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [C_22] :
      ( ~ r1_tarski(k2_relat_1(C_22),'#skF_3')
      | k1_relat_1(C_22) != '#skF_4'
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_3')
    | k1_relat_1(k1_xboole_0) != '#skF_4'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_56])).

tff(c_61,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_20,c_10,c_59])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_61])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_68])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_177,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_6])).

tff(c_204,plain,(
    ! [A_51] :
      ( v1_funct_1(A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_208,plain,(
    v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_204])).

tff(c_175,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_20])).

tff(c_174,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_10])).

tff(c_176,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_166,c_18])).

tff(c_167,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_182,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_167])).

tff(c_209,plain,(
    ! [C_52] :
      ( ~ r1_tarski(k2_relat_1(C_52),'#skF_4')
      | k1_relat_1(C_52) != '#skF_4'
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_32])).

tff(c_212,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_209])).

tff(c_214,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_175,c_174,c_212])).

tff(c_215,plain,(
    ! [A_53] :
      ( v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_215])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.25  
% 2.12/1.27  tff(f_84, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.12/1.27  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.12/1.27  tff(f_66, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.12/1.27  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.12/1.27  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.27  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.27  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.12/1.27  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.12/1.27  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.27  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.27  tff(c_34, plain, (k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.27  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.12/1.27  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.27  tff(c_26, plain, (![A_11, B_15]: (k1_relat_1('#skF_2'(A_11, B_15))=A_11 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.27  tff(c_28, plain, (![A_11, B_15]: (v1_funct_1('#skF_2'(A_11, B_15)) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.27  tff(c_30, plain, (![A_11, B_15]: (v1_relat_1('#skF_2'(A_11, B_15)) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.27  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.12/1.27  tff(c_94, plain, (![A_37, B_38]: (k2_relat_1('#skF_2'(A_37, B_38))=k1_tarski(B_38) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.27  tff(c_32, plain, (![C_18]: (~r1_tarski(k2_relat_1(C_18), '#skF_3') | k1_relat_1(C_18)!='#skF_4' | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.27  tff(c_106, plain, (![B_39, A_40]: (~r1_tarski(k1_tarski(B_39), '#skF_3') | k1_relat_1('#skF_2'(A_40, B_39))!='#skF_4' | ~v1_funct_1('#skF_2'(A_40, B_39)) | ~v1_relat_1('#skF_2'(A_40, B_39)) | k1_xboole_0=A_40)), inference(superposition, [status(thm), theory('equality')], [c_94, c_32])).
% 2.12/1.27  tff(c_111, plain, (![A_41, A_42]: (k1_relat_1('#skF_2'(A_41, A_42))!='#skF_4' | ~v1_funct_1('#skF_2'(A_41, A_42)) | ~v1_relat_1('#skF_2'(A_41, A_42)) | k1_xboole_0=A_41 | ~r2_hidden(A_42, '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_106])).
% 2.12/1.27  tff(c_116, plain, (![A_43, B_44]: (k1_relat_1('#skF_2'(A_43, B_44))!='#skF_4' | ~v1_funct_1('#skF_2'(A_43, B_44)) | ~r2_hidden(B_44, '#skF_3') | k1_xboole_0=A_43)), inference(resolution, [status(thm)], [c_30, c_111])).
% 2.12/1.27  tff(c_121, plain, (![A_45, B_46]: (k1_relat_1('#skF_2'(A_45, B_46))!='#skF_4' | ~r2_hidden(B_46, '#skF_3') | k1_xboole_0=A_45)), inference(resolution, [status(thm)], [c_28, c_116])).
% 2.12/1.27  tff(c_124, plain, (![A_11, B_15]: (A_11!='#skF_4' | ~r2_hidden(B_15, '#skF_3') | k1_xboole_0=A_11 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_26, c_121])).
% 2.12/1.27  tff(c_126, plain, (![B_47]: (~r2_hidden(B_47, '#skF_3'))), inference(splitLeft, [status(thm)], [c_124])).
% 2.12/1.27  tff(c_131, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_126])).
% 2.12/1.27  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.27  tff(c_140, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_131, c_8])).
% 2.12/1.27  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_140])).
% 2.12/1.27  tff(c_148, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_124])).
% 2.12/1.27  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.27  tff(c_62, plain, (![A_23]: (v1_relat_1(A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.27  tff(c_66, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.12/1.27  tff(c_51, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.27  tff(c_55, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_51])).
% 2.12/1.27  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.27  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.12/1.27  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.27  tff(c_56, plain, (![C_22]: (~r1_tarski(k2_relat_1(C_22), '#skF_3') | k1_relat_1(C_22)!='#skF_4' | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.27  tff(c_59, plain, (~r1_tarski(k1_xboole_0, '#skF_3') | k1_relat_1(k1_xboole_0)!='#skF_4' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_56])).
% 2.12/1.27  tff(c_61, plain, (k1_xboole_0!='#skF_4' | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_55, c_20, c_10, c_59])).
% 2.12/1.27  tff(c_68, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_61])).
% 2.12/1.27  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_68])).
% 2.12/1.27  tff(c_166, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 2.12/1.27  tff(c_177, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_6])).
% 2.12/1.27  tff(c_204, plain, (![A_51]: (v1_funct_1(A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.27  tff(c_208, plain, (v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_204])).
% 2.12/1.27  tff(c_175, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_20])).
% 2.12/1.27  tff(c_174, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_10])).
% 2.12/1.27  tff(c_176, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_166, c_18])).
% 2.12/1.27  tff(c_167, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.12/1.27  tff(c_182, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_167])).
% 2.12/1.27  tff(c_209, plain, (![C_52]: (~r1_tarski(k2_relat_1(C_52), '#skF_4') | k1_relat_1(C_52)!='#skF_4' | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_32])).
% 2.12/1.27  tff(c_212, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_176, c_209])).
% 2.12/1.27  tff(c_214, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_175, c_174, c_212])).
% 2.12/1.27  tff(c_215, plain, (![A_53]: (v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.27  tff(c_218, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_177, c_215])).
% 2.12/1.27  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_218])).
% 2.12/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  Inference rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Ref     : 0
% 2.12/1.27  #Sup     : 36
% 2.12/1.27  #Fact    : 0
% 2.12/1.27  #Define  : 0
% 2.12/1.27  #Split   : 2
% 2.12/1.27  #Chain   : 0
% 2.12/1.27  #Close   : 0
% 2.12/1.27  
% 2.12/1.27  Ordering : KBO
% 2.12/1.27  
% 2.12/1.27  Simplification rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Subsume      : 3
% 2.12/1.27  #Demod        : 35
% 2.12/1.27  #Tautology    : 20
% 2.12/1.27  #SimpNegUnit  : 2
% 2.12/1.27  #BackRed      : 20
% 2.12/1.27  
% 2.12/1.27  #Partial instantiations: 0
% 2.12/1.27  #Strategies tried      : 1
% 2.12/1.27  
% 2.12/1.27  Timing (in seconds)
% 2.12/1.27  ----------------------
% 2.12/1.27  Preprocessing        : 0.28
% 2.12/1.27  Parsing              : 0.15
% 2.12/1.27  CNF conversion       : 0.02
% 2.12/1.27  Main loop            : 0.18
% 2.12/1.27  Inferencing          : 0.07
% 2.12/1.27  Reduction            : 0.05
% 2.12/1.27  Demodulation         : 0.03
% 2.12/1.27  BG Simplification    : 0.01
% 2.12/1.27  Subsumption          : 0.03
% 2.12/1.27  Abstraction          : 0.01
% 2.12/1.27  MUC search           : 0.00
% 2.12/1.27  Cooper               : 0.00
% 2.12/1.27  Total                : 0.50
% 2.12/1.27  Index Insertion      : 0.00
% 2.12/1.27  Index Deletion       : 0.00
% 2.12/1.27  Index Matching       : 0.00
% 2.12/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
