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
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  91 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_43] : k1_relat_1('#skF_2'(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_43] : v1_relat_1('#skF_2'(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) != k1_xboole_0
      | k1_xboole_0 = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_66,plain,(
    ! [A_43] :
      ( k1_relat_1('#skF_2'(A_43)) != k1_xboole_0
      | '#skF_2'(A_43) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_63])).

tff(c_73,plain,(
    '#skF_2'(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_32,plain,(
    ! [A_43] : v1_funct_1('#skF_2'(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_204,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),k1_relat_1(B_94))
      | v5_funct_1(B_94,A_93)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_210,plain,(
    ! [A_93,A_43] :
      ( r2_hidden('#skF_1'(A_93,'#skF_2'(A_43)),A_43)
      | v5_funct_1('#skF_2'(A_43),A_93)
      | ~ v1_funct_1('#skF_2'(A_43))
      | ~ v1_relat_1('#skF_2'(A_43))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_204])).

tff(c_214,plain,(
    ! [A_95,A_96] :
      ( r2_hidden('#skF_1'(A_95,'#skF_2'(A_96)),A_96)
      | v5_funct_1('#skF_2'(A_96),A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_210])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [A_60,C_61,B_62] :
      ( ~ r2_hidden(A_60,C_61)
      | ~ r1_xboole_0(k2_tarski(A_60,B_62),C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_138])).

tff(c_221,plain,(
    ! [A_95] :
      ( v5_funct_1('#skF_2'(k1_xboole_0),A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_214,c_143])).

tff(c_228,plain,(
    ! [A_97] :
      ( v5_funct_1(k1_xboole_0,A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_221])).

tff(c_36,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_231,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_36])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:18:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.28  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff(np__1, type, np__1: $i).
% 1.97/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.28  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.97/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.97/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.28  
% 1.97/1.29  tff(f_87, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.97/1.29  tff(f_80, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 1.97/1.29  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.97/1.29  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.97/1.29  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.29  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.97/1.29  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.29  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.29  tff(c_30, plain, (![A_43]: (k1_relat_1('#skF_2'(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.97/1.29  tff(c_34, plain, (![A_43]: (v1_relat_1('#skF_2'(A_43)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.97/1.29  tff(c_63, plain, (![A_54]: (k1_relat_1(A_54)!=k1_xboole_0 | k1_xboole_0=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.97/1.29  tff(c_66, plain, (![A_43]: (k1_relat_1('#skF_2'(A_43))!=k1_xboole_0 | '#skF_2'(A_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_63])).
% 1.97/1.29  tff(c_73, plain, ('#skF_2'(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 1.97/1.29  tff(c_32, plain, (![A_43]: (v1_funct_1('#skF_2'(A_43)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.97/1.29  tff(c_204, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), k1_relat_1(B_94)) | v5_funct_1(B_94, A_93) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.29  tff(c_210, plain, (![A_93, A_43]: (r2_hidden('#skF_1'(A_93, '#skF_2'(A_43)), A_43) | v5_funct_1('#skF_2'(A_43), A_93) | ~v1_funct_1('#skF_2'(A_43)) | ~v1_relat_1('#skF_2'(A_43)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_30, c_204])).
% 1.97/1.29  tff(c_214, plain, (![A_95, A_96]: (r2_hidden('#skF_1'(A_95, '#skF_2'(A_96)), A_96) | v5_funct_1('#skF_2'(A_96), A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_210])).
% 1.97/1.29  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.29  tff(c_138, plain, (![A_60, C_61, B_62]: (~r2_hidden(A_60, C_61) | ~r1_xboole_0(k2_tarski(A_60, B_62), C_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.29  tff(c_143, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_138])).
% 1.97/1.29  tff(c_221, plain, (![A_95]: (v5_funct_1('#skF_2'(k1_xboole_0), A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_214, c_143])).
% 1.97/1.29  tff(c_228, plain, (![A_97]: (v5_funct_1(k1_xboole_0, A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_221])).
% 1.97/1.29  tff(c_36, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 1.97/1.29  tff(c_231, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_228, c_36])).
% 1.97/1.29  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_231])).
% 1.97/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  Inference rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Ref     : 3
% 1.97/1.29  #Sup     : 36
% 1.97/1.29  #Fact    : 0
% 1.97/1.29  #Define  : 0
% 1.97/1.29  #Split   : 4
% 1.97/1.29  #Chain   : 0
% 1.97/1.29  #Close   : 0
% 1.97/1.29  
% 1.97/1.29  Ordering : KBO
% 1.97/1.29  
% 1.97/1.29  Simplification rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Subsume      : 9
% 1.97/1.29  #Demod        : 7
% 1.97/1.29  #Tautology    : 21
% 1.97/1.29  #SimpNegUnit  : 6
% 1.97/1.29  #BackRed      : 0
% 1.97/1.29  
% 1.97/1.29  #Partial instantiations: 0
% 1.97/1.29  #Strategies tried      : 1
% 1.97/1.29  
% 1.97/1.29  Timing (in seconds)
% 1.97/1.29  ----------------------
% 1.97/1.29  Preprocessing        : 0.32
% 1.97/1.30  Parsing              : 0.17
% 1.97/1.30  CNF conversion       : 0.02
% 1.97/1.30  Main loop            : 0.17
% 1.97/1.30  Inferencing          : 0.07
% 1.97/1.30  Reduction            : 0.05
% 1.97/1.30  Demodulation         : 0.03
% 1.97/1.30  BG Simplification    : 0.02
% 1.97/1.30  Subsumption          : 0.02
% 1.97/1.30  Abstraction          : 0.01
% 1.97/1.30  MUC search           : 0.00
% 1.97/1.30  Cooper               : 0.00
% 1.97/1.30  Total                : 0.51
% 1.97/1.30  Index Insertion      : 0.00
% 1.97/1.30  Index Deletion       : 0.00
% 1.97/1.30  Index Matching       : 0.00
% 1.97/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
