%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 (  83 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_6 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_44,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
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

tff(c_34,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,k3_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_6,C_46] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_68,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [C_47] : ~ r2_hidden(C_47,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    ! [A_38] :
      ( v1_funct_1(A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [A_57,B_58] :
      ( r2_hidden('#skF_5'(A_57,B_58),k1_relat_1(B_58))
      | v5_funct_1(B_58,A_57)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_5'(A_57,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_57)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_106])).

tff(c_111,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_5'(A_57,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_48,c_109])).

tff(c_113,plain,(
    ! [A_59] :
      ( v5_funct_1(k1_xboole_0,A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_111])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_113,c_30])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:19:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/2.00  
% 2.19/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/2.01  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_6 > #skF_1 > #skF_5 > #skF_4
% 2.19/2.01  
% 2.19/2.01  %Foreground sorts:
% 2.19/2.01  
% 2.19/2.01  
% 2.19/2.01  %Background operators:
% 2.19/2.01  
% 2.19/2.01  
% 2.19/2.01  %Foreground operators:
% 2.19/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.19/2.01  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.19/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/2.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/2.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/2.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.19/2.01  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.19/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/2.01  tff('#skF_6', type, '#skF_6': $i).
% 2.19/2.01  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/2.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.19/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/2.01  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.19/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/2.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.19/2.01  
% 2.19/2.04  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.19/2.04  tff(f_44, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/2.04  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.19/2.04  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.19/2.04  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.19/2.04  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.19/2.04  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.19/2.04  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.19/2.04  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.19/2.04  tff(c_34, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/2.04  tff(c_32, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/2.04  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/2.04  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/2.04  tff(c_58, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/2.04  tff(c_65, plain, (![A_6, C_46]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_58])).
% 2.19/2.04  tff(c_68, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65])).
% 2.19/2.04  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/2.04  tff(c_69, plain, (![C_47]: (~r2_hidden(C_47, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65])).
% 2.19/2.04  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_69])).
% 2.19/2.04  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.19/2.04  tff(c_44, plain, (![A_38]: (v1_funct_1(A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.19/2.04  tff(c_48, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 2.19/2.04  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/2.04  tff(c_106, plain, (![A_57, B_58]: (r2_hidden('#skF_5'(A_57, B_58), k1_relat_1(B_58)) | v5_funct_1(B_58, A_57) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.19/2.04  tff(c_109, plain, (![A_57]: (r2_hidden('#skF_5'(A_57, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_57) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_20, c_106])).
% 2.19/2.04  tff(c_111, plain, (![A_57]: (r2_hidden('#skF_5'(A_57, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_48, c_109])).
% 2.19/2.04  tff(c_113, plain, (![A_59]: (v5_funct_1(k1_xboole_0, A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(negUnitSimplification, [status(thm)], [c_68, c_111])).
% 2.19/2.04  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.19/2.04  tff(c_116, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_113, c_30])).
% 2.19/2.04  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_116])).
% 2.19/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/2.04  
% 2.19/2.04  Inference rules
% 2.19/2.04  ----------------------
% 2.19/2.04  #Ref     : 1
% 2.19/2.04  #Sup     : 18
% 2.19/2.04  #Fact    : 0
% 2.19/2.04  #Define  : 0
% 2.19/2.04  #Split   : 0
% 2.19/2.04  #Chain   : 0
% 2.19/2.04  #Close   : 0
% 2.19/2.04  
% 2.19/2.04  Ordering : KBO
% 2.19/2.04  
% 2.19/2.04  Simplification rules
% 2.19/2.04  ----------------------
% 2.19/2.04  #Subsume      : 0
% 2.19/2.04  #Demod        : 8
% 2.19/2.04  #Tautology    : 11
% 2.19/2.04  #SimpNegUnit  : 2
% 2.19/2.04  #BackRed      : 0
% 2.19/2.04  
% 2.19/2.04  #Partial instantiations: 0
% 2.19/2.04  #Strategies tried      : 1
% 2.19/2.04  
% 2.19/2.04  Timing (in seconds)
% 2.19/2.04  ----------------------
% 2.19/2.05  Preprocessing        : 0.60
% 2.19/2.05  Parsing              : 0.33
% 2.33/2.05  CNF conversion       : 0.06
% 2.33/2.05  Main loop            : 0.36
% 2.33/2.05  Inferencing          : 0.15
% 2.33/2.05  Reduction            : 0.12
% 2.33/2.05  Demodulation         : 0.09
% 2.33/2.05  BG Simplification    : 0.03
% 2.33/2.05  Subsumption          : 0.04
% 2.33/2.05  Abstraction          : 0.01
% 2.33/2.05  MUC search           : 0.00
% 2.33/2.05  Cooper               : 0.00
% 2.33/2.05  Total                : 1.03
% 2.33/2.05  Index Insertion      : 0.00
% 2.33/2.05  Index Deletion       : 0.00
% 2.33/2.05  Index Matching       : 0.00
% 2.33/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
