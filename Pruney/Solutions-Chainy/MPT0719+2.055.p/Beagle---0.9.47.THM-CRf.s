%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:50 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   46 (  78 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 143 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_31,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_34,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_50,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [A_18] :
      ( k7_relat_1(A_18,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k7_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_53,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_53])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_59])).

tff(c_4,plain,(
    ! [A_2] : k10_relat_1(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [B_25,A_26] :
      ( k10_relat_1(B_25,k1_tarski(A_26)) != k1_xboole_0
      | ~ r2_hidden(A_26,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [A_26] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_26)) != k1_xboole_0
      | ~ r2_hidden(A_26,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_122])).

tff(c_127,plain,(
    ! [A_26] : ~ r2_hidden(A_26,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4,c_125])).

tff(c_76,plain,(
    ! [A_21,B_22] :
      ( v1_funct_1(k7_relat_1(A_21,B_22))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_76])).

tff(c_86,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_82])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_139,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_1'(A_30,B_31),k1_relat_1(B_31))
      | v5_funct_1(B_31,A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_30)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_144,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_86,c_142])).

tff(c_146,plain,(
    ! [A_32] :
      ( v5_funct_1(k1_xboole_0,A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_144])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_24])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  
% 1.77/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.21  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.21  
% 1.77/1.21  %Foreground sorts:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Background operators:
% 1.77/1.21  
% 1.77/1.21  
% 1.77/1.21  %Foreground operators:
% 1.77/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.21  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.77/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.77/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.77/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.21  
% 1.86/1.22  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.86/1.22  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.86/1.22  tff(f_58, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 1.86/1.22  tff(f_31, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.86/1.22  tff(f_34, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.86/1.22  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 1.86/1.22  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.86/1.22  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.22  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.22  tff(c_44, plain, (![A_18]: (k7_relat_1(A_18, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.22  tff(c_48, plain, (k7_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_44])).
% 1.86/1.22  tff(c_53, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.22  tff(c_59, plain, (v1_relat_1(k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_53])).
% 1.86/1.22  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_59])).
% 1.86/1.22  tff(c_4, plain, (![A_2]: (k10_relat_1(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.22  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.86/1.22  tff(c_122, plain, (![B_25, A_26]: (k10_relat_1(B_25, k1_tarski(A_26))!=k1_xboole_0 | ~r2_hidden(A_26, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.86/1.22  tff(c_125, plain, (![A_26]: (k10_relat_1(k1_xboole_0, k1_tarski(A_26))!=k1_xboole_0 | ~r2_hidden(A_26, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_122])).
% 1.86/1.22  tff(c_127, plain, (![A_26]: (~r2_hidden(A_26, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4, c_125])).
% 1.86/1.22  tff(c_76, plain, (![A_21, B_22]: (v1_funct_1(k7_relat_1(A_21, B_22)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.22  tff(c_82, plain, (v1_funct_1(k1_xboole_0) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_76])).
% 1.86/1.22  tff(c_86, plain, (v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_82])).
% 1.86/1.22  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.86/1.22  tff(c_139, plain, (![A_30, B_31]: (r2_hidden('#skF_1'(A_30, B_31), k1_relat_1(B_31)) | v5_funct_1(B_31, A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.22  tff(c_142, plain, (![A_30]: (r2_hidden('#skF_1'(A_30, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_30) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_139])).
% 1.86/1.22  tff(c_144, plain, (![A_30]: (r2_hidden('#skF_1'(A_30, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_86, c_142])).
% 1.86/1.22  tff(c_146, plain, (![A_32]: (v5_funct_1(k1_xboole_0, A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(negUnitSimplification, [status(thm)], [c_127, c_144])).
% 1.86/1.22  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.22  tff(c_149, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_146, c_24])).
% 1.86/1.22  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_149])).
% 1.86/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  Inference rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Ref     : 0
% 1.86/1.22  #Sup     : 30
% 1.86/1.22  #Fact    : 0
% 1.86/1.22  #Define  : 0
% 1.86/1.22  #Split   : 0
% 1.86/1.22  #Chain   : 0
% 1.86/1.22  #Close   : 0
% 1.86/1.22  
% 1.86/1.22  Ordering : KBO
% 1.86/1.22  
% 1.86/1.22  Simplification rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Subsume      : 0
% 1.86/1.22  #Demod        : 25
% 1.86/1.22  #Tautology    : 22
% 1.86/1.22  #SimpNegUnit  : 1
% 1.86/1.22  #BackRed      : 0
% 1.86/1.22  
% 1.86/1.22  #Partial instantiations: 0
% 1.86/1.22  #Strategies tried      : 1
% 1.86/1.22  
% 1.86/1.22  Timing (in seconds)
% 1.86/1.22  ----------------------
% 1.86/1.23  Preprocessing        : 0.28
% 1.86/1.23  Parsing              : 0.16
% 1.86/1.23  CNF conversion       : 0.02
% 1.86/1.23  Main loop            : 0.14
% 1.86/1.23  Inferencing          : 0.06
% 1.86/1.23  Reduction            : 0.04
% 1.86/1.23  Demodulation         : 0.03
% 1.86/1.23  BG Simplification    : 0.01
% 1.86/1.23  Subsumption          : 0.02
% 1.86/1.23  Abstraction          : 0.01
% 1.86/1.23  MUC search           : 0.00
% 1.86/1.23  Cooper               : 0.00
% 1.86/1.23  Total                : 0.44
% 1.86/1.23  Index Insertion      : 0.00
% 1.86/1.23  Index Deletion       : 0.00
% 1.86/1.23  Index Matching       : 0.00
% 1.86/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
