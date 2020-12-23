%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 105 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_39,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_39])).

tff(c_34,plain,(
    ! [A_25] :
      ( v1_funct_1(A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_172,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),k1_relat_1(B_46))
      | v5_funct_1(B_46,A_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_7,C_34] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_94])).

tff(c_99,plain,(
    ! [C_34] : ~ r2_hidden(C_34,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_97])).

tff(c_57,plain,(
    ! [A_29] :
      ( v1_xboole_0(k2_relat_1(A_29))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_70,plain,(
    ! [A_30] :
      ( k2_relat_1(A_30) = k1_xboole_0
      | ~ v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_78,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_151,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(k1_funct_1(B_40,A_41),k2_relat_1(B_40))
      | ~ r2_hidden(A_41,k1_relat_1(B_40))
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_157,plain,(
    ! [A_41] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_41),k1_xboole_0)
      | ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_151])).

tff(c_160,plain,(
    ! [A_41] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_41),k1_xboole_0)
      | ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_38,c_157])).

tff(c_161,plain,(
    ! [A_41] : ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_160])).

tff(c_180,plain,(
    ! [A_45] :
      ( v5_funct_1(k1_xboole_0,A_45)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_172,c_161])).

tff(c_185,plain,(
    ! [A_47] :
      ( v5_funct_1(k1_xboole_0,A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_38,c_180])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_188,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_28])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  
% 1.94/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.19  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.94/1.19  
% 1.94/1.19  %Foreground sorts:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Background operators:
% 1.94/1.19  
% 1.94/1.19  
% 1.94/1.19  %Foreground operators:
% 1.94/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.19  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.94/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.94/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.19  
% 1.94/1.20  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.94/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/1.20  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.94/1.20  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.94/1.20  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.94/1.20  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.94/1.20  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.94/1.20  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.94/1.20  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.94/1.20  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.20  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.94/1.20  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.94/1.20  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.94/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.94/1.20  tff(c_39, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.20  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_39])).
% 1.94/1.20  tff(c_34, plain, (![A_25]: (v1_funct_1(A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.20  tff(c_38, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_34])).
% 1.94/1.20  tff(c_172, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), k1_relat_1(B_46)) | v5_funct_1(B_46, A_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.20  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.94/1.20  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.20  tff(c_94, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.94/1.20  tff(c_97, plain, (![A_7, C_34]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_94])).
% 1.94/1.20  tff(c_99, plain, (![C_34]: (~r2_hidden(C_34, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_97])).
% 1.94/1.20  tff(c_57, plain, (![A_29]: (v1_xboole_0(k2_relat_1(A_29)) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.94/1.20  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.94/1.20  tff(c_70, plain, (![A_30]: (k2_relat_1(A_30)=k1_xboole_0 | ~v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_57, c_4])).
% 1.94/1.20  tff(c_78, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_70])).
% 1.94/1.20  tff(c_151, plain, (![B_40, A_41]: (r2_hidden(k1_funct_1(B_40, A_41), k2_relat_1(B_40)) | ~r2_hidden(A_41, k1_relat_1(B_40)) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.94/1.20  tff(c_157, plain, (![A_41]: (r2_hidden(k1_funct_1(k1_xboole_0, A_41), k1_xboole_0) | ~r2_hidden(A_41, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_151])).
% 1.94/1.20  tff(c_160, plain, (![A_41]: (r2_hidden(k1_funct_1(k1_xboole_0, A_41), k1_xboole_0) | ~r2_hidden(A_41, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_38, c_157])).
% 1.94/1.20  tff(c_161, plain, (![A_41]: (~r2_hidden(A_41, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_99, c_160])).
% 1.94/1.20  tff(c_180, plain, (![A_45]: (v5_funct_1(k1_xboole_0, A_45) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_172, c_161])).
% 1.94/1.20  tff(c_185, plain, (![A_47]: (v5_funct_1(k1_xboole_0, A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_38, c_180])).
% 1.94/1.20  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 1.94/1.20  tff(c_188, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_28])).
% 1.94/1.20  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_188])).
% 1.94/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  Inference rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Ref     : 0
% 1.94/1.20  #Sup     : 33
% 1.94/1.20  #Fact    : 0
% 1.94/1.20  #Define  : 0
% 1.94/1.20  #Split   : 0
% 1.94/1.20  #Chain   : 0
% 1.94/1.20  #Close   : 0
% 1.94/1.20  
% 1.94/1.20  Ordering : KBO
% 1.94/1.20  
% 1.94/1.20  Simplification rules
% 1.94/1.20  ----------------------
% 1.94/1.20  #Subsume      : 2
% 1.94/1.20  #Demod        : 26
% 1.94/1.20  #Tautology    : 18
% 1.94/1.20  #SimpNegUnit  : 3
% 1.94/1.20  #BackRed      : 0
% 1.94/1.20  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.29
% 1.94/1.21  Parsing              : 0.17
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.15
% 1.94/1.21  Inferencing          : 0.07
% 1.94/1.21  Reduction            : 0.04
% 1.94/1.21  Demodulation         : 0.03
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.47
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
