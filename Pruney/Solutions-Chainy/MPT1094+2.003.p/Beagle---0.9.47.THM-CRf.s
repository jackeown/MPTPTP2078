%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 134 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k7_funct_3 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k7_funct_3,type,(
    k7_funct_3: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k9_funct_3,type,(
    k9_funct_3: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
        <=> v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(k7_funct_3(A,B))
      & v1_funct_1(k7_funct_3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_3)).

tff(f_49,axiom,(
    ! [A,B] : k9_funct_3(A,B) = k7_funct_3(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_funct_3)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_finset_1(k1_relat_1(A))
       => v1_finset_1(k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_finset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( v1_finset_1(k1_relat_1('#skF_1'))
    | v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    v1_finset_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_30])).

tff(c_4,plain,(
    ! [A_2,B_3] : v1_relat_1(k7_funct_3(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_2,B_3] : v1_funct_1(k7_funct_3(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_8,B_9] : k9_funct_3(A_8,B_9) = k7_funct_3(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(A_10),k2_relat_1(A_10)),A_10) = k1_relat_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [A_30] :
      ( k9_relat_1(k7_funct_3(k1_relat_1(A_30),k2_relat_1(A_30)),A_30) = k1_relat_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_finset_1(k9_relat_1(A_4,B_5))
      | ~ v1_finset_1(B_5)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_30] :
      ( v1_finset_1(k1_relat_1(A_30))
      | ~ v1_finset_1(A_30)
      | ~ v1_funct_1(k7_funct_3(k1_relat_1(A_30),k2_relat_1(A_30)))
      | ~ v1_relat_1(k7_funct_3(k1_relat_1(A_30),k2_relat_1(A_30)))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_8])).

tff(c_78,plain,(
    ! [A_31] :
      ( v1_finset_1(k1_relat_1(A_31))
      | ~ v1_finset_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_70])).

tff(c_81,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_34])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_35,c_81])).

tff(c_86,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_87,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_finset_1(k2_relat_1(A_13))
      | ~ v1_finset_1(k1_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( v1_finset_1(k2_zfmisc_1(A_6,B_7))
      | ~ v1_finset_1(B_7)
      | ~ v1_finset_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,k2_zfmisc_1(k1_relat_1(A_38),k2_relat_1(A_38)))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_finset_1(A_11)
      | ~ v1_finset_1(B_12)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    ! [A_42] :
      ( v1_finset_1(A_42)
      | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42)))
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_101,c_16])).

tff(c_113,plain,(
    ! [A_43] :
      ( v1_finset_1(A_43)
      | ~ v1_relat_1(A_43)
      | ~ v1_finset_1(k2_relat_1(A_43))
      | ~ v1_finset_1(k1_relat_1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_118,plain,(
    ! [A_44] :
      ( v1_finset_1(A_44)
      | ~ v1_finset_1(k1_relat_1(A_44))
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_18,c_113])).

tff(c_121,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_118])).

tff(c_124,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_121])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k7_funct_3 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.22  tff(k7_funct_3, type, k7_funct_3: ($i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(k9_funct_3, type, k9_funct_3: ($i * $i) > $i).
% 1.98/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.98/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.22  
% 2.08/1.23  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) <=> v1_finset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_finset_1)).
% 2.08/1.23  tff(f_33, axiom, (![A, B]: (v1_relat_1(k7_funct_3(A, B)) & v1_funct_1(k7_funct_3(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_3)).
% 2.08/1.23  tff(f_49, axiom, (![A, B]: (k9_funct_3(A, B) = k7_funct_3(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_funct_3)).
% 2.08/1.23  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (k9_relat_1(k9_funct_3(k1_relat_1(A), k2_relat_1(A)), A) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_funct_3)).
% 2.08/1.23  tff(f_41, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 2.08/1.23  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) => v1_finset_1(k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 2.08/1.23  tff(f_47, axiom, (![A, B]: ((v1_finset_1(A) & v1_finset_1(B)) => v1_finset_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_finset_1)).
% 2.08/1.23  tff(f_29, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.08/1.23  tff(f_61, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 2.08/1.23  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.23  tff(c_20, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.23  tff(c_24, plain, (~v1_finset_1('#skF_1') | ~v1_finset_1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.23  tff(c_34, plain, (~v1_finset_1(k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.08/1.23  tff(c_30, plain, (v1_finset_1(k1_relat_1('#skF_1')) | v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.23  tff(c_35, plain, (v1_finset_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_30])).
% 2.08/1.23  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k7_funct_3(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.23  tff(c_6, plain, (![A_2, B_3]: (v1_funct_1(k7_funct_3(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.23  tff(c_12, plain, (![A_8, B_9]: (k9_funct_3(A_8, B_9)=k7_funct_3(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.23  tff(c_14, plain, (![A_10]: (k9_relat_1(k9_funct_3(k1_relat_1(A_10), k2_relat_1(A_10)), A_10)=k1_relat_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.23  tff(c_64, plain, (![A_30]: (k9_relat_1(k7_funct_3(k1_relat_1(A_30), k2_relat_1(A_30)), A_30)=k1_relat_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.08/1.23  tff(c_8, plain, (![A_4, B_5]: (v1_finset_1(k9_relat_1(A_4, B_5)) | ~v1_finset_1(B_5) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.23  tff(c_70, plain, (![A_30]: (v1_finset_1(k1_relat_1(A_30)) | ~v1_finset_1(A_30) | ~v1_funct_1(k7_funct_3(k1_relat_1(A_30), k2_relat_1(A_30))) | ~v1_relat_1(k7_funct_3(k1_relat_1(A_30), k2_relat_1(A_30))) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_64, c_8])).
% 2.08/1.23  tff(c_78, plain, (![A_31]: (v1_finset_1(k1_relat_1(A_31)) | ~v1_finset_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_70])).
% 2.08/1.23  tff(c_81, plain, (~v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_78, c_34])).
% 2.08/1.23  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_35, c_81])).
% 2.08/1.23  tff(c_86, plain, (~v1_finset_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.08/1.23  tff(c_87, plain, (v1_finset_1(k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_24])).
% 2.08/1.23  tff(c_18, plain, (![A_13]: (v1_finset_1(k2_relat_1(A_13)) | ~v1_finset_1(k1_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.23  tff(c_10, plain, (![A_6, B_7]: (v1_finset_1(k2_zfmisc_1(A_6, B_7)) | ~v1_finset_1(B_7) | ~v1_finset_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.23  tff(c_101, plain, (![A_38]: (r1_tarski(A_38, k2_zfmisc_1(k1_relat_1(A_38), k2_relat_1(A_38))) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.23  tff(c_16, plain, (![A_11, B_12]: (v1_finset_1(A_11) | ~v1_finset_1(B_12) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.23  tff(c_108, plain, (![A_42]: (v1_finset_1(A_42) | ~v1_finset_1(k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42))) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_101, c_16])).
% 2.08/1.23  tff(c_113, plain, (![A_43]: (v1_finset_1(A_43) | ~v1_relat_1(A_43) | ~v1_finset_1(k2_relat_1(A_43)) | ~v1_finset_1(k1_relat_1(A_43)))), inference(resolution, [status(thm)], [c_10, c_108])).
% 2.08/1.23  tff(c_118, plain, (![A_44]: (v1_finset_1(A_44) | ~v1_finset_1(k1_relat_1(A_44)) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_18, c_113])).
% 2.08/1.23  tff(c_121, plain, (v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_87, c_118])).
% 2.08/1.23  tff(c_124, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_121])).
% 2.08/1.23  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_124])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 15
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 1
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 0
% 2.08/1.23  #Demod        : 9
% 2.08/1.23  #Tautology    : 9
% 2.08/1.23  #SimpNegUnit  : 3
% 2.08/1.23  #BackRed      : 0
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.30
% 2.08/1.23  Parsing              : 0.16
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.14
% 2.08/1.23  Inferencing          : 0.06
% 2.08/1.23  Reduction            : 0.04
% 2.08/1.23  Demodulation         : 0.03
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.02
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.47
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
