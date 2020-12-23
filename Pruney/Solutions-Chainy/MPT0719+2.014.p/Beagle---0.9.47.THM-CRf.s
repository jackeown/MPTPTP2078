%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 (  99 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_73,axiom,(
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

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_49,plain,(
    ! [A_38] :
      ( v1_funct_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_195,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),k1_relat_1(B_68))
      | v5_funct_1(B_68,A_67)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_hidden(A_46,C_47)
      | ~ r1_xboole_0(k2_tarski(A_46,B_48),C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_54,plain,(
    ! [A_39] :
      ( v1_xboole_0(k2_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_69,plain,(
    ! [A_42] :
      ( k2_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_77,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_174,plain,(
    ! [B_62,A_63] :
      ( r2_hidden(k1_funct_1(B_62,A_63),k2_relat_1(B_62))
      | ~ r2_hidden(A_63,k1_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_180,plain,(
    ! [A_63] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_63),k1_xboole_0)
      | ~ r2_hidden(A_63,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_174])).

tff(c_183,plain,(
    ! [A_63] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,A_63),k1_xboole_0)
      | ~ r2_hidden(A_63,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_53,c_180])).

tff(c_184,plain,(
    ! [A_63] : ~ r2_hidden(A_63,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_183])).

tff(c_203,plain,(
    ! [A_67] :
      ( v5_funct_1(k1_xboole_0,A_67)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_195,c_184])).

tff(c_208,plain,(
    ! [A_69] :
      ( v5_funct_1(k1_xboole_0,A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_53,c_203])).

tff(c_32,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_211,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_208,c_32])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.22  
% 2.16/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.22  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.22  
% 2.16/1.22  %Foreground sorts:
% 2.16/1.22  
% 2.16/1.22  
% 2.16/1.22  %Background operators:
% 2.16/1.22  
% 2.16/1.22  
% 2.16/1.22  %Foreground operators:
% 2.16/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.16/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.22  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.16/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.16/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.22  
% 2.27/1.23  tff(f_88, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.27/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.27/1.23  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.27/1.23  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.27/1.23  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.27/1.23  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.27/1.23  tff(f_45, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.27/1.23  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.27/1.23  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.23  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.27/1.23  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.23  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.27/1.23  tff(c_44, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.23  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.27/1.23  tff(c_49, plain, (![A_38]: (v1_funct_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.23  tff(c_53, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.27/1.23  tff(c_195, plain, (![A_67, B_68]: (r2_hidden('#skF_1'(A_67, B_68), k1_relat_1(B_68)) | v5_funct_1(B_68, A_67) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.27/1.23  tff(c_6, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.23  tff(c_140, plain, (![A_46, C_47, B_48]: (~r2_hidden(A_46, C_47) | ~r1_xboole_0(k2_tarski(A_46, B_48), C_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.23  tff(c_145, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.27/1.23  tff(c_54, plain, (![A_39]: (v1_xboole_0(k2_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.27/1.23  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.27/1.23  tff(c_69, plain, (![A_42]: (k2_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_54, c_4])).
% 2.27/1.23  tff(c_77, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.27/1.23  tff(c_174, plain, (![B_62, A_63]: (r2_hidden(k1_funct_1(B_62, A_63), k2_relat_1(B_62)) | ~r2_hidden(A_63, k1_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.27/1.23  tff(c_180, plain, (![A_63]: (r2_hidden(k1_funct_1(k1_xboole_0, A_63), k1_xboole_0) | ~r2_hidden(A_63, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_77, c_174])).
% 2.27/1.23  tff(c_183, plain, (![A_63]: (r2_hidden(k1_funct_1(k1_xboole_0, A_63), k1_xboole_0) | ~r2_hidden(A_63, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_53, c_180])).
% 2.27/1.23  tff(c_184, plain, (![A_63]: (~r2_hidden(A_63, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_145, c_183])).
% 2.27/1.23  tff(c_203, plain, (![A_67]: (v5_funct_1(k1_xboole_0, A_67) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_195, c_184])).
% 2.27/1.23  tff(c_208, plain, (![A_69]: (v5_funct_1(k1_xboole_0, A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_53, c_203])).
% 2.27/1.23  tff(c_32, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.23  tff(c_211, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_208, c_32])).
% 2.27/1.23  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_211])).
% 2.27/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.23  
% 2.27/1.23  Inference rules
% 2.27/1.23  ----------------------
% 2.27/1.23  #Ref     : 0
% 2.27/1.23  #Sup     : 37
% 2.27/1.23  #Fact    : 0
% 2.27/1.23  #Define  : 0
% 2.27/1.23  #Split   : 0
% 2.27/1.23  #Chain   : 0
% 2.27/1.23  #Close   : 0
% 2.27/1.23  
% 2.27/1.23  Ordering : KBO
% 2.27/1.23  
% 2.27/1.23  Simplification rules
% 2.27/1.23  ----------------------
% 2.27/1.23  #Subsume      : 2
% 2.27/1.23  #Demod        : 24
% 2.27/1.23  #Tautology    : 22
% 2.27/1.23  #SimpNegUnit  : 2
% 2.27/1.23  #BackRed      : 0
% 2.27/1.23  
% 2.27/1.23  #Partial instantiations: 0
% 2.27/1.23  #Strategies tried      : 1
% 2.27/1.23  
% 2.27/1.23  Timing (in seconds)
% 2.27/1.23  ----------------------
% 2.27/1.24  Preprocessing        : 0.32
% 2.27/1.24  Parsing              : 0.18
% 2.27/1.24  CNF conversion       : 0.02
% 2.27/1.24  Main loop            : 0.16
% 2.27/1.24  Inferencing          : 0.07
% 2.27/1.24  Reduction            : 0.05
% 2.27/1.24  Demodulation         : 0.04
% 2.27/1.24  BG Simplification    : 0.02
% 2.27/1.24  Subsumption          : 0.02
% 2.27/1.24  Abstraction          : 0.01
% 2.27/1.24  MUC search           : 0.00
% 2.27/1.24  Cooper               : 0.00
% 2.27/1.24  Total                : 0.51
% 2.27/1.24  Index Insertion      : 0.00
% 2.27/1.24  Index Deletion       : 0.00
% 2.27/1.24  Index Matching       : 0.00
% 2.27/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
