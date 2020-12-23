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
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 104 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 276 expanded)
%              Number of equality atoms :   10 (  37 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_74,axiom,(
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

tff(f_47,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [B_30,A_31] :
      ( k5_relat_1(B_30,k6_relat_1(A_31)) = k8_relat_1(A_31,B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_31,B_30] :
      ( v1_relat_1(k8_relat_1(A_31,B_30))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_68,plain,(
    ! [A_31,B_30] :
      ( v1_relat_1(k8_relat_1(A_31,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_78,plain,(
    ! [D_38,C_39,A_40] :
      ( r2_hidden(D_38,k1_relat_1(C_39))
      | ~ r2_hidden(D_38,k1_relat_1(k8_relat_1(A_40,C_39)))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39)
      | ~ v1_funct_1(k8_relat_1(A_40,C_39))
      | ~ v1_relat_1(k8_relat_1(A_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

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
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_94,plain,(
    v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [A_7] : v1_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = k8_relat_1(A_3,B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_34,B_35] :
      ( v1_funct_1(k5_relat_1(A_34,B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

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
    inference(cnfTransformation,[status(thm)],[f_74])).

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
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.52  
% 2.53/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.52  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.53/1.52  
% 2.53/1.52  %Foreground sorts:
% 2.53/1.52  
% 2.53/1.52  
% 2.53/1.52  %Background operators:
% 2.53/1.52  
% 2.53/1.52  
% 2.53/1.52  %Foreground operators:
% 2.53/1.52  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.53/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.53/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.53/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.52  tff('#skF_6', type, '#skF_6': $i).
% 2.53/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.53/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.53/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.53/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.53/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.52  
% 2.57/1.53  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_1)).
% 2.57/1.53  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.57/1.53  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.57/1.53  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.57/1.53  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 2.57/1.53  tff(f_47, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 2.57/1.53  tff(c_46, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.53  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.53  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.53  tff(c_56, plain, (![B_30, A_31]: (k5_relat_1(B_30, k6_relat_1(A_31))=k8_relat_1(A_31, B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.53  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.53  tff(c_62, plain, (![A_31, B_30]: (v1_relat_1(k8_relat_1(A_31, B_30)) | ~v1_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(B_30) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.57/1.53  tff(c_68, plain, (![A_31, B_30]: (v1_relat_1(k8_relat_1(A_31, B_30)) | ~v1_relat_1(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_62])).
% 2.57/1.53  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.53  tff(c_48, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.57/1.53  tff(c_78, plain, (![D_38, C_39, A_40]: (r2_hidden(D_38, k1_relat_1(C_39)) | ~r2_hidden(D_38, k1_relat_1(k8_relat_1(A_40, C_39))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39) | ~v1_funct_1(k8_relat_1(A_40, C_39)) | ~v1_relat_1(k8_relat_1(A_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.53  tff(c_81, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_78])).
% 2.57/1.53  tff(c_84, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_81])).
% 2.57/1.53  tff(c_85, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.57/1.53  tff(c_88, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_85])).
% 2.57/1.53  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_88])).
% 2.57/1.53  tff(c_94, plain, (v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 2.57/1.53  tff(c_12, plain, (![A_7]: (v1_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.53  tff(c_4, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=k8_relat_1(A_3, B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.53  tff(c_71, plain, (![A_34, B_35]: (v1_funct_1(k5_relat_1(A_34, B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.53  tff(c_74, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_relat_1(B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_71])).
% 2.57/1.53  tff(c_76, plain, (![A_3, B_4]: (v1_funct_1(k8_relat_1(A_3, B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_74])).
% 2.57/1.53  tff(c_93, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_84])).
% 2.57/1.53  tff(c_102, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.57/1.53  tff(c_105, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_102])).
% 2.57/1.53  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_105])).
% 2.57/1.53  tff(c_111, plain, (v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_93])).
% 2.57/1.53  tff(c_118, plain, (![A_44, C_45, D_46]: (k1_funct_1(k8_relat_1(A_44, C_45), D_46)=k1_funct_1(C_45, D_46) | ~r2_hidden(D_46, k1_relat_1(k8_relat_1(A_44, C_45))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(k8_relat_1(A_44, C_45)) | ~v1_relat_1(k8_relat_1(A_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.53  tff(c_121, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_118])).
% 2.57/1.53  tff(c_124, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_111, c_52, c_50, c_121])).
% 2.57/1.53  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_124])).
% 2.57/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.53  
% 2.57/1.53  Inference rules
% 2.57/1.53  ----------------------
% 2.57/1.53  #Ref     : 0
% 2.57/1.53  #Sup     : 9
% 2.57/1.53  #Fact    : 0
% 2.57/1.53  #Define  : 0
% 2.57/1.53  #Split   : 3
% 2.57/1.53  #Chain   : 0
% 2.57/1.53  #Close   : 0
% 2.57/1.53  
% 2.57/1.53  Ordering : KBO
% 2.57/1.54  
% 2.57/1.54  Simplification rules
% 2.57/1.54  ----------------------
% 2.57/1.54  #Subsume      : 1
% 2.57/1.54  #Demod        : 17
% 2.57/1.54  #Tautology    : 3
% 2.57/1.54  #SimpNegUnit  : 1
% 2.57/1.54  #BackRed      : 0
% 2.57/1.54  
% 2.57/1.54  #Partial instantiations: 0
% 2.57/1.54  #Strategies tried      : 1
% 2.57/1.54  
% 2.57/1.54  Timing (in seconds)
% 2.57/1.54  ----------------------
% 2.57/1.54  Preprocessing        : 0.50
% 2.57/1.54  Parsing              : 0.26
% 2.57/1.54  CNF conversion       : 0.04
% 2.57/1.54  Main loop            : 0.20
% 2.57/1.54  Inferencing          : 0.06
% 2.57/1.54  Reduction            : 0.06
% 2.57/1.54  Demodulation         : 0.04
% 2.57/1.54  BG Simplification    : 0.03
% 2.57/1.54  Subsumption          : 0.05
% 2.57/1.54  Abstraction          : 0.01
% 2.57/1.54  MUC search           : 0.00
% 2.57/1.54  Cooper               : 0.00
% 2.57/1.54  Total                : 0.73
% 2.57/1.54  Index Insertion      : 0.00
% 2.57/1.54  Index Deletion       : 0.00
% 2.57/1.54  Index Matching       : 0.00
% 2.57/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
