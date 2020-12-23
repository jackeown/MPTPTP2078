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
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  88 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_40,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_143,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_59)
      | r2_hidden('#skF_2'(A_58,B_59),A_58)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    ! [B_40,A_41] :
      ( ~ r2_hidden(B_40,A_41)
      | k4_xboole_0(A_41,k1_tarski(B_40)) != A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [B_40] : ~ r2_hidden(B_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_86])).

tff(c_157,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_59),B_59)
      | k1_xboole_0 = B_59 ) ),
    inference(resolution,[status(thm)],[c_143,c_91])).

tff(c_169,plain,(
    ! [C_61,A_62] :
      ( r2_hidden(k4_tarski(C_61,'#skF_6'(A_62,k1_relat_1(A_62),C_61)),A_62)
      | ~ r2_hidden(C_61,k1_relat_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_169,c_91])).

tff(c_187,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157,c_179])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_187])).

tff(c_209,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_286,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_84)
      | r2_hidden('#skF_2'(A_83,B_84),A_83)
      | B_84 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_215,plain,(
    ! [B_64,A_65] :
      ( ~ r2_hidden(B_64,A_65)
      | k4_xboole_0(A_65,k1_tarski(B_64)) != A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    ! [B_64] : ~ r2_hidden(B_64,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_215])).

tff(c_311,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_85),B_85)
      | k1_xboole_0 = B_85 ) ),
    inference(resolution,[status(thm)],[c_286,c_220])).

tff(c_49,plain,(
    ! [B_37] : k2_zfmisc_1(k1_xboole_0,B_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_36])).

tff(c_210,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_266,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_7'(A_78,B_79),k1_relat_1(B_79))
      | ~ r2_hidden(A_78,k2_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_7'(A_78,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_78,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_266])).

tff(c_271,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_7'(A_78,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_78,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_269])).

tff(c_272,plain,(
    ! [A_78] : ~ r2_hidden(A_78,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_271])).

tff(c_315,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_272])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_315])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.26  
% 1.83/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.27  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.83/1.27  
% 1.83/1.27  %Foreground sorts:
% 1.83/1.27  
% 1.83/1.27  
% 1.83/1.27  %Background operators:
% 1.83/1.27  
% 1.83/1.27  
% 1.83/1.27  %Foreground operators:
% 1.83/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.83/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.83/1.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.83/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.83/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.27  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.83/1.27  
% 1.83/1.28  tff(f_70, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.28  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 1.83/1.28  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.83/1.28  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.83/1.28  tff(f_55, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.83/1.28  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.83/1.28  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.83/1.28  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.83/1.28  tff(c_40, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.83/1.28  tff(c_85, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 1.83/1.28  tff(c_143, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58, B_59), B_59) | r2_hidden('#skF_2'(A_58, B_59), A_58) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.28  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.28  tff(c_86, plain, (![B_40, A_41]: (~r2_hidden(B_40, A_41) | k4_xboole_0(A_41, k1_tarski(B_40))!=A_41)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.28  tff(c_91, plain, (![B_40]: (~r2_hidden(B_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_86])).
% 1.83/1.28  tff(c_157, plain, (![B_59]: (r2_hidden('#skF_1'(k1_xboole_0, B_59), B_59) | k1_xboole_0=B_59)), inference(resolution, [status(thm)], [c_143, c_91])).
% 1.83/1.28  tff(c_169, plain, (![C_61, A_62]: (r2_hidden(k4_tarski(C_61, '#skF_6'(A_62, k1_relat_1(A_62), C_61)), A_62) | ~r2_hidden(C_61, k1_relat_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.28  tff(c_179, plain, (![C_63]: (~r2_hidden(C_63, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_169, c_91])).
% 1.83/1.28  tff(c_187, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_157, c_179])).
% 1.83/1.28  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_187])).
% 1.83/1.28  tff(c_209, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 1.83/1.28  tff(c_286, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84), B_84) | r2_hidden('#skF_2'(A_83, B_84), A_83) | B_84=A_83)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.83/1.28  tff(c_215, plain, (![B_64, A_65]: (~r2_hidden(B_64, A_65) | k4_xboole_0(A_65, k1_tarski(B_64))!=A_65)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.83/1.28  tff(c_220, plain, (![B_64]: (~r2_hidden(B_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_215])).
% 1.83/1.28  tff(c_311, plain, (![B_85]: (r2_hidden('#skF_1'(k1_xboole_0, B_85), B_85) | k1_xboole_0=B_85)), inference(resolution, [status(thm)], [c_286, c_220])).
% 1.83/1.28  tff(c_49, plain, (![B_37]: (k2_zfmisc_1(k1_xboole_0, B_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.83/1.28  tff(c_36, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.83/1.28  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49, c_36])).
% 1.83/1.28  tff(c_210, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 1.83/1.28  tff(c_266, plain, (![A_78, B_79]: (r2_hidden('#skF_7'(A_78, B_79), k1_relat_1(B_79)) | ~r2_hidden(A_78, k2_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.83/1.28  tff(c_269, plain, (![A_78]: (r2_hidden('#skF_7'(A_78, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_78, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_210, c_266])).
% 1.83/1.28  tff(c_271, plain, (![A_78]: (r2_hidden('#skF_7'(A_78, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_78, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_269])).
% 1.83/1.28  tff(c_272, plain, (![A_78]: (~r2_hidden(A_78, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_220, c_271])).
% 1.83/1.28  tff(c_315, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_272])).
% 1.83/1.28  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_315])).
% 1.83/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.28  
% 1.83/1.28  Inference rules
% 1.83/1.28  ----------------------
% 1.83/1.28  #Ref     : 0
% 1.83/1.28  #Sup     : 55
% 1.83/1.28  #Fact    : 0
% 1.83/1.28  #Define  : 0
% 1.83/1.28  #Split   : 1
% 1.83/1.28  #Chain   : 0
% 1.83/1.28  #Close   : 0
% 1.83/1.28  
% 1.83/1.28  Ordering : KBO
% 1.83/1.28  
% 1.83/1.28  Simplification rules
% 1.83/1.28  ----------------------
% 1.83/1.28  #Subsume      : 4
% 1.83/1.28  #Demod        : 2
% 1.83/1.28  #Tautology    : 33
% 1.83/1.28  #SimpNegUnit  : 5
% 1.83/1.28  #BackRed      : 0
% 1.83/1.28  
% 1.83/1.28  #Partial instantiations: 0
% 1.83/1.28  #Strategies tried      : 1
% 1.83/1.28  
% 1.83/1.28  Timing (in seconds)
% 1.83/1.28  ----------------------
% 1.83/1.28  Preprocessing        : 0.29
% 1.83/1.28  Parsing              : 0.15
% 1.83/1.28  CNF conversion       : 0.02
% 1.83/1.28  Main loop            : 0.19
% 1.83/1.28  Inferencing          : 0.08
% 1.83/1.28  Reduction            : 0.05
% 1.83/1.28  Demodulation         : 0.03
% 1.83/1.28  BG Simplification    : 0.01
% 1.83/1.28  Subsumption          : 0.03
% 1.83/1.28  Abstraction          : 0.01
% 1.83/1.28  MUC search           : 0.00
% 1.83/1.28  Cooper               : 0.00
% 1.83/1.28  Total                : 0.50
% 1.83/1.28  Index Insertion      : 0.00
% 1.83/1.28  Index Deletion       : 0.00
% 1.83/1.28  Index Matching       : 0.00
% 1.83/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
