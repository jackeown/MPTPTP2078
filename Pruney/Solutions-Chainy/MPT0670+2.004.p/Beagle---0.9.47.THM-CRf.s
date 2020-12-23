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
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   50 (  98 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 261 expanded)
%              Number of equality atoms :    9 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(c_46,plain,(
    k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_78,plain,(
    ! [D_38,C_39,A_40] :
      ( r2_hidden(D_38,k1_relat_1(C_39))
      | ~ r2_hidden(D_38,k1_relat_1(k8_relat_1(A_40,C_39)))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(k8_relat_1(A_40,C_39))
      | ~ v1_relat_1(k8_relat_1(A_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_81,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_78])).

tff(c_84,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_81])).

tff(c_85,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_88,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_94,plain,(
    v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_34,B_35] :
      ( v1_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_71])).

tff(c_76,plain,(
    ! [A_3,B_4] :
      ( v1_funct_1(k8_relat_1(A_3,B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_74])).

tff(c_93,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_102,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_105,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_105])).

tff(c_111,plain,(
    v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_118,plain,(
    ! [A_44,C_45,D_46] :
      ( k1_funct_1(k8_relat_1(A_44,C_45),D_46) = k1_funct_1(C_45,D_46)
      | ~ r2_hidden(D_46,k1_relat_1(k8_relat_1(A_44,C_45)))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(k8_relat_1(A_44,C_45))
      | ~ v1_relat_1(k8_relat_1(A_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_121,plain,
    ( k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') = k1_funct_1('#skF_6','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_118])).

tff(c_124,plain,(
    k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') = k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_111,c_52,c_50,c_121])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.20  
% 2.04/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.21  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.04/1.21  
% 2.04/1.21  %Foreground sorts:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Background operators:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Foreground operators:
% 2.04/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.04/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.04/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.04/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.21  tff('#skF_6', type, '#skF_6': $i).
% 2.04/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.21  
% 2.04/1.22  tff(f_81, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 2.04/1.22  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.04/1.22  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 2.04/1.22  tff(f_49, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.04/1.22  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.04/1.22  tff(f_45, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.04/1.22  tff(c_46, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.22  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.22  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.22  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.22  tff(c_48, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.22  tff(c_78, plain, (![D_38, C_39, A_40]: (r2_hidden(D_38, k1_relat_1(C_39)) | ~r2_hidden(D_38, k1_relat_1(k8_relat_1(A_40, C_39))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(k8_relat_1(A_40, C_39)) | ~v1_relat_1(k8_relat_1(A_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.22  tff(c_81, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_78])).
% 2.04/1.22  tff(c_84, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_81])).
% 2.04/1.22  tff(c_85, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.04/1.22  tff(c_88, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_85])).
% 2.04/1.22  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_88])).
% 2.04/1.22  tff(c_94, plain, (v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 2.04/1.22  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.22  tff(c_12, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.22  tff(c_4, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.22  tff(c_71, plain, (![A_34, B_35]: (v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.22  tff(c_74, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_71])).
% 2.04/1.22  tff(c_76, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_74])).
% 2.04/1.22  tff(c_93, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 2.04/1.22  tff(c_102, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.04/1.22  tff(c_105, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_102])).
% 2.04/1.22  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_105])).
% 2.04/1.22  tff(c_111, plain, (v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_93])).
% 2.04/1.22  tff(c_118, plain, (![A_44, C_45, D_46]: (k1_funct_1(k8_relat_1(A_44, C_45), D_46)=k1_funct_1(C_45, D_46) | ~r2_hidden(D_46, k1_relat_1(k8_relat_1(A_44, C_45))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(k8_relat_1(A_44, C_45)) | ~v1_relat_1(k8_relat_1(A_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.04/1.22  tff(c_121, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_118])).
% 2.04/1.22  tff(c_124, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_111, c_52, c_50, c_121])).
% 2.04/1.22  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_124])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 9
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 3
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 1
% 2.04/1.22  #Demod        : 18
% 2.04/1.22  #Tautology    : 3
% 2.04/1.22  #SimpNegUnit  : 1
% 2.04/1.22  #BackRed      : 0
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.22  Preprocessing        : 0.30
% 2.04/1.22  Parsing              : 0.15
% 2.04/1.22  CNF conversion       : 0.03
% 2.04/1.22  Main loop            : 0.17
% 2.04/1.22  Inferencing          : 0.05
% 2.04/1.22  Reduction            : 0.05
% 2.04/1.22  Demodulation         : 0.04
% 2.04/1.22  BG Simplification    : 0.02
% 2.04/1.22  Subsumption          : 0.05
% 2.04/1.22  Abstraction          : 0.01
% 2.04/1.22  MUC search           : 0.00
% 2.04/1.22  Cooper               : 0.00
% 2.04/1.22  Total                : 0.50
% 2.04/1.22  Index Insertion      : 0.00
% 2.04/1.22  Index Deletion       : 0.00
% 2.04/1.22  Index Matching       : 0.00
% 2.04/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
