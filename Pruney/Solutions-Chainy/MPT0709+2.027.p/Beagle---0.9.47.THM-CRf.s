%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 111 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_18,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k10_relat_1(B_6,A_5),k1_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k9_relat_1(B_4,A_3),k2_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [B_28,A_29] :
      ( k9_relat_1(B_28,k10_relat_1(B_28,A_29)) = A_29
      | ~ r1_tarski(A_29,k2_relat_1(B_28))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [B_4,A_3] :
      ( k9_relat_1(B_4,k10_relat_1(B_4,k9_relat_1(B_4,A_3))) = k9_relat_1(B_4,A_3)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_172,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_tarski(A_35,B_36)
      | ~ v2_funct_1(C_37)
      | ~ r1_tarski(A_35,k1_relat_1(C_37))
      | ~ r1_tarski(k9_relat_1(C_37,A_35),k9_relat_1(C_37,B_36))
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1027,plain,(
    ! [B_76,A_77,B_78] :
      ( r1_tarski(k10_relat_1(B_76,k9_relat_1(B_76,A_77)),B_78)
      | ~ v2_funct_1(B_76)
      | ~ r1_tarski(k10_relat_1(B_76,k9_relat_1(B_76,A_77)),k1_relat_1(B_76))
      | ~ r1_tarski(k9_relat_1(B_76,A_77),k9_relat_1(B_76,B_78))
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_172])).

tff(c_1060,plain,(
    ! [B_79,A_80,B_81] :
      ( r1_tarski(k10_relat_1(B_79,k9_relat_1(B_79,A_80)),B_81)
      | ~ v2_funct_1(B_79)
      | ~ r1_tarski(k9_relat_1(B_79,A_80),k9_relat_1(B_79,B_81))
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_10,c_1027])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,k10_relat_1(B_22,k9_relat_1(B_22,A_21)))
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_1067,plain,(
    ! [B_79,B_81] :
      ( k10_relat_1(B_79,k9_relat_1(B_79,B_81)) = B_81
      | ~ r1_tarski(B_81,k1_relat_1(B_79))
      | ~ v2_funct_1(B_79)
      | ~ r1_tarski(k9_relat_1(B_79,B_81),k9_relat_1(B_79,B_81))
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_1060,c_51])).

tff(c_1115,plain,(
    ! [B_82,B_83] :
      ( k10_relat_1(B_82,k9_relat_1(B_82,B_83)) = B_83
      | ~ r1_tarski(B_83,k1_relat_1(B_82))
      | ~ v2_funct_1(B_82)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1067])).

tff(c_1125,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1115])).

tff(c_1134,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_1125])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.30/1.54  
% 3.30/1.54  %Foreground sorts:
% 3.30/1.54  
% 3.30/1.54  
% 3.30/1.54  %Background operators:
% 3.30/1.54  
% 3.30/1.54  
% 3.30/1.54  %Foreground operators:
% 3.30/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.30/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.30/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.54  
% 3.40/1.55  tff(f_76, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.40/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.55  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.40/1.55  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.40/1.55  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.40/1.55  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 3.40/1.55  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.40/1.55  tff(c_18, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_20, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.40/1.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.55  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k10_relat_1(B_6, A_5), k1_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.55  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k9_relat_1(B_4, A_3), k2_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.55  tff(c_84, plain, (![B_28, A_29]: (k9_relat_1(B_28, k10_relat_1(B_28, A_29))=A_29 | ~r1_tarski(A_29, k2_relat_1(B_28)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.55  tff(c_90, plain, (![B_4, A_3]: (k9_relat_1(B_4, k10_relat_1(B_4, k9_relat_1(B_4, A_3)))=k9_relat_1(B_4, A_3) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_8, c_84])).
% 3.40/1.55  tff(c_172, plain, (![A_35, B_36, C_37]: (r1_tarski(A_35, B_36) | ~v2_funct_1(C_37) | ~r1_tarski(A_35, k1_relat_1(C_37)) | ~r1_tarski(k9_relat_1(C_37, A_35), k9_relat_1(C_37, B_36)) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.55  tff(c_1027, plain, (![B_76, A_77, B_78]: (r1_tarski(k10_relat_1(B_76, k9_relat_1(B_76, A_77)), B_78) | ~v2_funct_1(B_76) | ~r1_tarski(k10_relat_1(B_76, k9_relat_1(B_76, A_77)), k1_relat_1(B_76)) | ~r1_tarski(k9_relat_1(B_76, A_77), k9_relat_1(B_76, B_78)) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_90, c_172])).
% 3.40/1.55  tff(c_1060, plain, (![B_79, A_80, B_81]: (r1_tarski(k10_relat_1(B_79, k9_relat_1(B_79, A_80)), B_81) | ~v2_funct_1(B_79) | ~r1_tarski(k9_relat_1(B_79, A_80), k9_relat_1(B_79, B_81)) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_10, c_1027])).
% 3.40/1.55  tff(c_48, plain, (![A_21, B_22]: (r1_tarski(A_21, k10_relat_1(B_22, k9_relat_1(B_22, A_21))) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.55  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.55  tff(c_51, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_48, c_2])).
% 3.40/1.55  tff(c_1067, plain, (![B_79, B_81]: (k10_relat_1(B_79, k9_relat_1(B_79, B_81))=B_81 | ~r1_tarski(B_81, k1_relat_1(B_79)) | ~v2_funct_1(B_79) | ~r1_tarski(k9_relat_1(B_79, B_81), k9_relat_1(B_79, B_81)) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_1060, c_51])).
% 3.40/1.55  tff(c_1115, plain, (![B_82, B_83]: (k10_relat_1(B_82, k9_relat_1(B_82, B_83))=B_83 | ~r1_tarski(B_83, k1_relat_1(B_82)) | ~v2_funct_1(B_82) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1067])).
% 3.40/1.55  tff(c_1125, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1115])).
% 3.40/1.55  tff(c_1134, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_1125])).
% 3.40/1.55  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_1134])).
% 3.40/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  Inference rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Ref     : 0
% 3.40/1.55  #Sup     : 294
% 3.40/1.55  #Fact    : 0
% 3.40/1.55  #Define  : 0
% 3.40/1.55  #Split   : 1
% 3.40/1.55  #Chain   : 0
% 3.40/1.55  #Close   : 0
% 3.40/1.55  
% 3.40/1.55  Ordering : KBO
% 3.40/1.55  
% 3.40/1.55  Simplification rules
% 3.40/1.55  ----------------------
% 3.40/1.55  #Subsume      : 96
% 3.40/1.55  #Demod        : 75
% 3.40/1.55  #Tautology    : 71
% 3.40/1.55  #SimpNegUnit  : 1
% 3.40/1.55  #BackRed      : 0
% 3.40/1.55  
% 3.40/1.55  #Partial instantiations: 0
% 3.40/1.55  #Strategies tried      : 1
% 3.40/1.55  
% 3.40/1.55  Timing (in seconds)
% 3.40/1.55  ----------------------
% 3.40/1.56  Preprocessing        : 0.28
% 3.40/1.56  Parsing              : 0.16
% 3.40/1.56  CNF conversion       : 0.02
% 3.40/1.56  Main loop            : 0.46
% 3.40/1.56  Inferencing          : 0.18
% 3.40/1.56  Reduction            : 0.13
% 3.40/1.56  Demodulation         : 0.09
% 3.40/1.56  BG Simplification    : 0.02
% 3.40/1.56  Subsumption          : 0.11
% 3.40/1.56  Abstraction          : 0.03
% 3.40/1.56  MUC search           : 0.00
% 3.40/1.56  Cooper               : 0.00
% 3.40/1.56  Total                : 0.77
% 3.40/1.56  Index Insertion      : 0.00
% 3.40/1.56  Index Deletion       : 0.00
% 3.40/1.56  Index Matching       : 0.00
% 3.40/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
