%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 110 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_23] :
      ( k3_xboole_0(A_23,k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23))) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_306,plain,(
    ! [A_115,C_116,B_117] :
      ( r2_hidden(A_115,C_116)
      | ~ r2_hidden(A_115,B_117)
      | r2_hidden(A_115,k5_xboole_0(B_117,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_260,plain,(
    ! [A_98,B_99] : k4_xboole_0(k2_xboole_0(A_98,B_99),k3_xboole_0(A_98,B_99)) = k5_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_266,plain,(
    ! [D_6,A_98,B_99] :
      ( ~ r2_hidden(D_6,k3_xboole_0(A_98,B_99))
      | ~ r2_hidden(D_6,k5_xboole_0(A_98,B_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_4])).

tff(c_328,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r2_hidden(A_121,k3_xboole_0(B_122,C_123))
      | r2_hidden(A_121,C_123)
      | ~ r2_hidden(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_306,c_266])).

tff(c_461,plain,(
    ! [A_143,A_144] :
      ( ~ r2_hidden(A_143,A_144)
      | r2_hidden(A_143,k2_zfmisc_1(k1_relat_1(A_144),k2_relat_1(A_144)))
      | ~ r2_hidden(A_143,A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_328])).

tff(c_44,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(k2_mcart_1(A_24),C_26)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_559,plain,(
    ! [A_152,A_153] :
      ( r2_hidden(k2_mcart_1(A_152),k2_relat_1(A_153))
      | ~ r2_hidden(A_152,A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_461,c_44])).

tff(c_145,plain,(
    ! [A_68,C_69,B_70] :
      ( r2_hidden(A_68,C_69)
      | ~ r2_hidden(A_68,B_70)
      | r2_hidden(A_68,k5_xboole_0(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_47,B_48] : k4_xboole_0(k2_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) = k5_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    ! [D_6,A_47,B_48] :
      ( ~ r2_hidden(D_6,k3_xboole_0(A_47,B_48))
      | ~ r2_hidden(D_6,k5_xboole_0(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_168,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r2_hidden(A_80,k3_xboole_0(B_81,C_82))
      | r2_hidden(A_80,C_82)
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_145,c_91])).

tff(c_229,plain,(
    ! [A_93,A_94] :
      ( ~ r2_hidden(A_93,A_94)
      | r2_hidden(A_93,k2_zfmisc_1(k1_relat_1(A_94),k2_relat_1(A_94)))
      | ~ r2_hidden(A_93,A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_168])).

tff(c_46,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k1_mcart_1(A_24),B_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_241,plain,(
    ! [A_95,A_96] :
      ( r2_hidden(k1_mcart_1(A_95),k1_relat_1(A_96))
      | ~ r2_hidden(A_95,A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_229,c_46])).

tff(c_48,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_244,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_241,c_84])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_244])).

tff(c_249,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_562,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_559,c_249])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.35  %$ r2_hidden > v1_relat_1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.54/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.54/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.54/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.54/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.35  
% 2.54/1.36  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 2.54/1.36  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.54/1.36  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.54/1.36  tff(f_44, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 2.54/1.36  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.54/1.36  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.54/1.36  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.36  tff(c_50, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.36  tff(c_42, plain, (![A_23]: (k3_xboole_0(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23)))=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.36  tff(c_306, plain, (![A_115, C_116, B_117]: (r2_hidden(A_115, C_116) | ~r2_hidden(A_115, B_117) | r2_hidden(A_115, k5_xboole_0(B_117, C_116)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.54/1.36  tff(c_260, plain, (![A_98, B_99]: (k4_xboole_0(k2_xboole_0(A_98, B_99), k3_xboole_0(A_98, B_99))=k5_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.36  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.36  tff(c_266, plain, (![D_6, A_98, B_99]: (~r2_hidden(D_6, k3_xboole_0(A_98, B_99)) | ~r2_hidden(D_6, k5_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_4])).
% 2.54/1.36  tff(c_328, plain, (![A_121, B_122, C_123]: (~r2_hidden(A_121, k3_xboole_0(B_122, C_123)) | r2_hidden(A_121, C_123) | ~r2_hidden(A_121, B_122))), inference(resolution, [status(thm)], [c_306, c_266])).
% 2.54/1.36  tff(c_461, plain, (![A_143, A_144]: (~r2_hidden(A_143, A_144) | r2_hidden(A_143, k2_zfmisc_1(k1_relat_1(A_144), k2_relat_1(A_144))) | ~r2_hidden(A_143, A_144) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_42, c_328])).
% 2.54/1.36  tff(c_44, plain, (![A_24, C_26, B_25]: (r2_hidden(k2_mcart_1(A_24), C_26) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.36  tff(c_559, plain, (![A_152, A_153]: (r2_hidden(k2_mcart_1(A_152), k2_relat_1(A_153)) | ~r2_hidden(A_152, A_153) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_461, c_44])).
% 2.54/1.36  tff(c_145, plain, (![A_68, C_69, B_70]: (r2_hidden(A_68, C_69) | ~r2_hidden(A_68, B_70) | r2_hidden(A_68, k5_xboole_0(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.54/1.36  tff(c_85, plain, (![A_47, B_48]: (k4_xboole_0(k2_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48))=k5_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.54/1.36  tff(c_91, plain, (![D_6, A_47, B_48]: (~r2_hidden(D_6, k3_xboole_0(A_47, B_48)) | ~r2_hidden(D_6, k5_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 2.54/1.36  tff(c_168, plain, (![A_80, B_81, C_82]: (~r2_hidden(A_80, k3_xboole_0(B_81, C_82)) | r2_hidden(A_80, C_82) | ~r2_hidden(A_80, B_81))), inference(resolution, [status(thm)], [c_145, c_91])).
% 2.54/1.36  tff(c_229, plain, (![A_93, A_94]: (~r2_hidden(A_93, A_94) | r2_hidden(A_93, k2_zfmisc_1(k1_relat_1(A_94), k2_relat_1(A_94))) | ~r2_hidden(A_93, A_94) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_42, c_168])).
% 2.54/1.36  tff(c_46, plain, (![A_24, B_25, C_26]: (r2_hidden(k1_mcart_1(A_24), B_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.36  tff(c_241, plain, (![A_95, A_96]: (r2_hidden(k1_mcart_1(A_95), k1_relat_1(A_96)) | ~r2_hidden(A_95, A_96) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_229, c_46])).
% 2.54/1.36  tff(c_48, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3')) | ~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.54/1.36  tff(c_84, plain, (~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.54/1.36  tff(c_244, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_241, c_84])).
% 2.54/1.36  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_244])).
% 2.54/1.36  tff(c_249, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 2.54/1.36  tff(c_562, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_559, c_249])).
% 2.54/1.36  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_562])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 0
% 2.54/1.36  #Sup     : 109
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 1
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 0
% 2.54/1.36  #Demod        : 4
% 2.54/1.36  #Tautology    : 38
% 2.54/1.36  #SimpNegUnit  : 0
% 2.54/1.36  #BackRed      : 0
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.54/1.37  Preprocessing        : 0.30
% 2.54/1.37  Parsing              : 0.16
% 2.54/1.37  CNF conversion       : 0.02
% 2.54/1.37  Main loop            : 0.29
% 2.54/1.37  Inferencing          : 0.12
% 2.54/1.37  Reduction            : 0.07
% 2.54/1.37  Demodulation         : 0.05
% 2.54/1.37  BG Simplification    : 0.02
% 2.54/1.37  Subsumption          : 0.06
% 2.54/1.37  Abstraction          : 0.02
% 2.54/1.37  MUC search           : 0.00
% 2.54/1.37  Cooper               : 0.00
% 2.54/1.37  Total                : 0.62
% 2.54/1.37  Index Insertion      : 0.00
% 2.54/1.37  Index Deletion       : 0.00
% 2.54/1.37  Index Matching       : 0.00
% 2.54/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
