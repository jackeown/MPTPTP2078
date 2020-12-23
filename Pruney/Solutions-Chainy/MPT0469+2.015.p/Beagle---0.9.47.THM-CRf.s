%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  86 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_76,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_12,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_82,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | k1_xboole_0 = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [C_54,A_55] :
      ( r2_hidden(k4_tarski(C_54,'#skF_5'(A_55,k1_relat_1(A_55),C_54)),A_55)
      | ~ r2_hidden(C_54,k1_relat_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_38,B_39] : ~ r2_hidden(A_38,k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_117,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_106,c_81])).

tff(c_129,plain,(
    ! [A_7] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_16,c_117])).

tff(c_164,plain,(
    ! [A_62] : ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_62)) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_129])).

tff(c_169,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_37,c_164])).

tff(c_170,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    ! [A_35] :
      ( v1_relat_1(A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_58,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_54])).

tff(c_171,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_197,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_6'(A_73,B_74),k1_relat_1(B_74))
      | ~ r2_hidden(A_73,k2_relat_1(B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_200,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_6'(A_73,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_73,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_197])).

tff(c_202,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_6'(A_73,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_73,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_200])).

tff(c_204,plain,(
    ! [A_75] : ~ r2_hidden(A_75,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_202])).

tff(c_208,plain,(
    ! [A_7] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_16,c_204])).

tff(c_212,plain,(
    ! [A_76] : ~ m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(A_76)) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_208])).

tff(c_217,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_37,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.97/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.97/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.97/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.97/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.21  
% 1.97/1.22  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.97/1.22  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.97/1.22  tff(f_76, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.97/1.22  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_subset_1)).
% 1.97/1.22  tff(f_63, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.97/1.22  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.97/1.22  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.97/1.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.22  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.97/1.22  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.97/1.22  tff(c_12, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_14, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.22  tff(c_37, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.97/1.22  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.97/1.22  tff(c_82, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_16, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | k1_xboole_0=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_106, plain, (![C_54, A_55]: (r2_hidden(k4_tarski(C_54, '#skF_5'(A_55, k1_relat_1(A_55), C_54)), A_55) | ~r2_hidden(C_54, k1_relat_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.22  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.22  tff(c_75, plain, (![A_38, B_39]: (~r2_hidden(A_38, k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.22  tff(c_81, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 1.97/1.22  tff(c_117, plain, (![C_59]: (~r2_hidden(C_59, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_106, c_81])).
% 1.97/1.22  tff(c_129, plain, (![A_7]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_16, c_117])).
% 1.97/1.22  tff(c_164, plain, (![A_62]: (~m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_62)))), inference(negUnitSimplification, [status(thm)], [c_82, c_129])).
% 1.97/1.22  tff(c_169, plain, $false, inference(resolution, [status(thm)], [c_37, c_164])).
% 1.97/1.22  tff(c_170, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.97/1.22  tff(c_54, plain, (![A_35]: (v1_relat_1(A_35) | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.22  tff(c_58, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_54])).
% 1.97/1.22  tff(c_171, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_197, plain, (![A_73, B_74]: (r2_hidden('#skF_6'(A_73, B_74), k1_relat_1(B_74)) | ~r2_hidden(A_73, k2_relat_1(B_74)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.22  tff(c_200, plain, (![A_73]: (r2_hidden('#skF_6'(A_73, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_73, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_197])).
% 1.97/1.22  tff(c_202, plain, (![A_73]: (r2_hidden('#skF_6'(A_73, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_73, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_200])).
% 1.97/1.22  tff(c_204, plain, (![A_75]: (~r2_hidden(A_75, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_81, c_202])).
% 1.97/1.22  tff(c_208, plain, (![A_7]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_16, c_204])).
% 1.97/1.22  tff(c_212, plain, (![A_76]: (~m1_subset_1(k2_relat_1(k1_xboole_0), k1_zfmisc_1(A_76)))), inference(negUnitSimplification, [status(thm)], [c_170, c_208])).
% 1.97/1.22  tff(c_217, plain, $false, inference(resolution, [status(thm)], [c_37, c_212])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 33
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 1
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 2
% 1.97/1.22  #Demod        : 3
% 1.97/1.22  #Tautology    : 17
% 1.97/1.22  #SimpNegUnit  : 3
% 1.97/1.22  #BackRed      : 0
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.29
% 1.97/1.22  Parsing              : 0.16
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.17
% 1.97/1.22  Inferencing          : 0.07
% 1.97/1.22  Reduction            : 0.04
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.03
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.48
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
