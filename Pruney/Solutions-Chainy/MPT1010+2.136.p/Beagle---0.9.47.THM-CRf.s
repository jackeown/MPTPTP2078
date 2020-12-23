%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:23 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   36 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 (  99 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_72,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,(
    ! [A_63] :
      ( k10_relat_1(A_63,k2_relat_1(A_63)) = k1_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,(
    ! [A_27] :
      ( k10_relat_1(k6_relat_1(A_27),A_27) = k1_relat_1(k6_relat_1(A_27))
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_129])).

tff(c_142,plain,(
    ! [A_27] : k10_relat_1(k6_relat_1(A_27),A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_138])).

tff(c_231,plain,(
    ! [B_96,A_97] :
      ( k10_relat_1(B_96,k1_tarski(A_97)) != k1_xboole_0
      | ~ r2_hidden(A_97,k2_relat_1(B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_237,plain,(
    ! [A_27,A_97] :
      ( k10_relat_1(k6_relat_1(A_27),k1_tarski(A_97)) != k1_xboole_0
      | ~ r2_hidden(A_97,A_27)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_231])).

tff(c_274,plain,(
    ! [A_116,A_117] :
      ( k10_relat_1(k6_relat_1(A_116),k1_tarski(A_117)) != k1_xboole_0
      | ~ r2_hidden(A_117,A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_237])).

tff(c_281,plain,(
    ! [A_117] :
      ( k1_tarski(A_117) != k1_xboole_0
      | ~ r2_hidden(A_117,k1_tarski(A_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_274])).

tff(c_284,plain,(
    ! [A_117] : k1_tarski(A_117) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_281])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_74,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_429,plain,(
    ! [D_142,C_143,B_144,A_145] :
      ( r2_hidden(k1_funct_1(D_142,C_143),B_144)
      | k1_xboole_0 = B_144
      | ~ r2_hidden(C_143,A_145)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_145,B_144)))
      | ~ v1_funct_2(D_142,A_145,B_144)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_569,plain,(
    ! [D_153,B_154] :
      ( r2_hidden(k1_funct_1(D_153,'#skF_7'),B_154)
      | k1_xboole_0 = B_154
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_154)))
      | ~ v1_funct_2(D_153,'#skF_5',B_154)
      | ~ v1_funct_1(D_153) ) ),
    inference(resolution,[status(thm)],[c_74,c_429])).

tff(c_572,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_569])).

tff(c_575,plain,
    ( r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6'))
    | k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_572])).

tff(c_576,plain,(
    r2_hidden(k1_funct_1('#skF_8','#skF_7'),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_575])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_581,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_576,c_2])).

tff(c_586,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.43  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.87/1.43  
% 2.87/1.43  %Foreground sorts:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Background operators:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Foreground operators:
% 2.87/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.87/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.43  
% 2.87/1.44  tff(f_101, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.87/1.44  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.87/1.44  tff(f_63, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.87/1.44  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.87/1.44  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.87/1.44  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.87/1.44  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.87/1.44  tff(c_72, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.44  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_58, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.44  tff(c_62, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.44  tff(c_64, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.44  tff(c_129, plain, (![A_63]: (k10_relat_1(A_63, k2_relat_1(A_63))=k1_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.44  tff(c_138, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=k1_relat_1(k6_relat_1(A_27)) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_129])).
% 2.87/1.44  tff(c_142, plain, (![A_27]: (k10_relat_1(k6_relat_1(A_27), A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_138])).
% 2.87/1.44  tff(c_231, plain, (![B_96, A_97]: (k10_relat_1(B_96, k1_tarski(A_97))!=k1_xboole_0 | ~r2_hidden(A_97, k2_relat_1(B_96)) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.44  tff(c_237, plain, (![A_27, A_97]: (k10_relat_1(k6_relat_1(A_27), k1_tarski(A_97))!=k1_xboole_0 | ~r2_hidden(A_97, A_27) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_231])).
% 2.87/1.44  tff(c_274, plain, (![A_116, A_117]: (k10_relat_1(k6_relat_1(A_116), k1_tarski(A_117))!=k1_xboole_0 | ~r2_hidden(A_117, A_116))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_237])).
% 2.87/1.44  tff(c_281, plain, (![A_117]: (k1_tarski(A_117)!=k1_xboole_0 | ~r2_hidden(A_117, k1_tarski(A_117)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_274])).
% 2.87/1.44  tff(c_284, plain, (![A_117]: (k1_tarski(A_117)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_281])).
% 2.87/1.44  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.44  tff(c_78, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.44  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.44  tff(c_74, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.87/1.44  tff(c_429, plain, (![D_142, C_143, B_144, A_145]: (r2_hidden(k1_funct_1(D_142, C_143), B_144) | k1_xboole_0=B_144 | ~r2_hidden(C_143, A_145) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_145, B_144))) | ~v1_funct_2(D_142, A_145, B_144) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.87/1.44  tff(c_569, plain, (![D_153, B_154]: (r2_hidden(k1_funct_1(D_153, '#skF_7'), B_154) | k1_xboole_0=B_154 | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_154))) | ~v1_funct_2(D_153, '#skF_5', B_154) | ~v1_funct_1(D_153))), inference(resolution, [status(thm)], [c_74, c_429])).
% 2.87/1.44  tff(c_572, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0 | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_76, c_569])).
% 2.87/1.44  tff(c_575, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6')) | k1_tarski('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_572])).
% 2.87/1.44  tff(c_576, plain, (r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_284, c_575])).
% 2.87/1.44  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.87/1.44  tff(c_581, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_576, c_2])).
% 2.87/1.44  tff(c_586, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_581])).
% 2.87/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  Inference rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Ref     : 0
% 2.87/1.44  #Sup     : 110
% 2.87/1.44  #Fact    : 0
% 2.87/1.44  #Define  : 0
% 2.87/1.44  #Split   : 0
% 2.87/1.44  #Chain   : 0
% 2.87/1.44  #Close   : 0
% 2.87/1.44  
% 2.87/1.44  Ordering : KBO
% 2.87/1.44  
% 2.87/1.44  Simplification rules
% 2.87/1.44  ----------------------
% 2.87/1.44  #Subsume      : 3
% 2.87/1.44  #Demod        : 31
% 2.87/1.44  #Tautology    : 55
% 2.87/1.44  #SimpNegUnit  : 2
% 2.87/1.44  #BackRed      : 0
% 2.87/1.44  
% 2.87/1.44  #Partial instantiations: 0
% 2.87/1.44  #Strategies tried      : 1
% 2.87/1.44  
% 2.87/1.44  Timing (in seconds)
% 2.87/1.44  ----------------------
% 2.87/1.44  Preprocessing        : 0.33
% 2.87/1.44  Parsing              : 0.16
% 2.87/1.44  CNF conversion       : 0.03
% 2.87/1.44  Main loop            : 0.32
% 2.87/1.44  Inferencing          : 0.12
% 2.87/1.44  Reduction            : 0.09
% 2.87/1.44  Demodulation         : 0.07
% 2.87/1.44  BG Simplification    : 0.02
% 2.87/1.44  Subsumption          : 0.08
% 2.87/1.44  Abstraction          : 0.03
% 2.87/1.44  MUC search           : 0.00
% 2.87/1.44  Cooper               : 0.00
% 2.87/1.44  Total                : 0.68
% 2.87/1.44  Index Insertion      : 0.00
% 2.87/1.44  Index Deletion       : 0.00
% 2.87/1.44  Index Matching       : 0.00
% 2.87/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
