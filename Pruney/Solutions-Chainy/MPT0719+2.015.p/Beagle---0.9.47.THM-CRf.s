%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 (  95 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_85,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_29] :
      ( v1_relat_1(A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_40,plain,(
    ! [A_27] :
      ( v1_funct_1(A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_172,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_3'(A_46,B_47),k1_relat_1(B_47))
      | v5_funct_1(B_47,A_46)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_81,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [A_7,C_36] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_81])).

tff(c_86,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_57,plain,(
    ! [A_30] :
      ( v1_xboole_0(k2_relat_1(A_30))
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) = k1_xboole_0
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_80,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_151,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_2'(A_41,B_42),k2_relat_1(B_42))
      | ~ r2_hidden(A_41,k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_157,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_2'(A_41,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_151])).

tff(c_160,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_2'(A_41,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_157])).

tff(c_161,plain,(
    ! [A_41] : ~ r2_hidden(A_41,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_160])).

tff(c_180,plain,(
    ! [A_46] :
      ( v5_funct_1(k1_xboole_0,A_46)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_172,c_161])).

tff(c_185,plain,(
    ! [A_48] :
      ( v5_funct_1(k1_xboole_0,A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_44,c_180])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_188,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_185,c_28])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.28  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.99/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.28  
% 1.99/1.29  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.99/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.99/1.29  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.99/1.29  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.99/1.29  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.99/1.29  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.99/1.29  tff(f_46, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.99/1.29  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.99/1.29  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.99/1.29  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.99/1.29  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 1.99/1.29  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.99/1.29  tff(c_52, plain, (![A_29]: (v1_relat_1(A_29) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.99/1.29  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 1.99/1.29  tff(c_40, plain, (![A_27]: (v1_funct_1(A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.29  tff(c_44, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_40])).
% 1.99/1.29  tff(c_172, plain, (![A_46, B_47]: (r2_hidden('#skF_3'(A_46, B_47), k1_relat_1(B_47)) | v5_funct_1(B_47, A_46) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.99/1.29  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.29  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.99/1.29  tff(c_81, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.29  tff(c_84, plain, (![A_7, C_36]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_81])).
% 1.99/1.29  tff(c_86, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_84])).
% 1.99/1.29  tff(c_57, plain, (![A_30]: (v1_xboole_0(k2_relat_1(A_30)) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.29  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.99/1.29  tff(c_72, plain, (![A_33]: (k2_relat_1(A_33)=k1_xboole_0 | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_57, c_4])).
% 1.99/1.29  tff(c_80, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_72])).
% 1.99/1.29  tff(c_151, plain, (![A_41, B_42]: (r2_hidden('#skF_2'(A_41, B_42), k2_relat_1(B_42)) | ~r2_hidden(A_41, k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.29  tff(c_157, plain, (![A_41]: (r2_hidden('#skF_2'(A_41, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_41, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_80, c_151])).
% 1.99/1.29  tff(c_160, plain, (![A_41]: (r2_hidden('#skF_2'(A_41, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_41, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_157])).
% 1.99/1.29  tff(c_161, plain, (![A_41]: (~r2_hidden(A_41, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_86, c_160])).
% 1.99/1.29  tff(c_180, plain, (![A_46]: (v5_funct_1(k1_xboole_0, A_46) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_172, c_161])).
% 1.99/1.29  tff(c_185, plain, (![A_48]: (v5_funct_1(k1_xboole_0, A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_44, c_180])).
% 1.99/1.29  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 1.99/1.29  tff(c_188, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_185, c_28])).
% 1.99/1.29  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_188])).
% 1.99/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  Inference rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Ref     : 0
% 1.99/1.29  #Sup     : 33
% 1.99/1.29  #Fact    : 0
% 1.99/1.29  #Define  : 0
% 1.99/1.29  #Split   : 0
% 1.99/1.29  #Chain   : 0
% 1.99/1.29  #Close   : 0
% 1.99/1.29  
% 1.99/1.29  Ordering : KBO
% 1.99/1.29  
% 1.99/1.29  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 2
% 1.99/1.29  #Demod        : 23
% 1.99/1.29  #Tautology    : 18
% 1.99/1.29  #SimpNegUnit  : 3
% 1.99/1.29  #BackRed      : 0
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.30  Preprocessing        : 0.31
% 1.99/1.30  Parsing              : 0.17
% 1.99/1.30  CNF conversion       : 0.02
% 1.99/1.30  Main loop            : 0.16
% 1.99/1.30  Inferencing          : 0.07
% 1.99/1.30  Reduction            : 0.04
% 1.99/1.30  Demodulation         : 0.03
% 1.99/1.30  BG Simplification    : 0.01
% 1.99/1.30  Subsumption          : 0.03
% 1.99/1.30  Abstraction          : 0.01
% 1.99/1.30  MUC search           : 0.00
% 1.99/1.30  Cooper               : 0.00
% 1.99/1.30  Total                : 0.50
% 1.99/1.30  Index Insertion      : 0.00
% 1.99/1.30  Index Deletion       : 0.00
% 1.99/1.30  Index Matching       : 0.00
% 1.99/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
