%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:26 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 141 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k7_relat_1 > k7_funct_3 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k7_funct_3,type,(
    k7_funct_3: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k9_funct_3,type,(
    k9_funct_3: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_finset_1(k1_relat_1(A))
        <=> v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(k7_funct_3(A,B))
      & v1_funct_1(k7_funct_3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

tff(f_65,axiom,(
    ! [A,B] : k9_funct_3(A,B) = k7_funct_3(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => k9_relat_1(k9_funct_3(k1_relat_1(A),k2_relat_1(A)),A) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_finset_1(B)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ~ v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( v1_finset_1(k1_relat_1('#skF_1'))
    | v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_41,plain,(
    v1_finset_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k7_funct_3(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_funct_1(k7_funct_3(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_15,B_16] : k9_funct_3(A_15,B_16) = k7_funct_3(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_17] :
      ( k9_relat_1(k9_funct_3(k1_relat_1(A_17),k2_relat_1(A_17)),A_17) = k1_relat_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,(
    ! [A_48] :
      ( k9_relat_1(k7_funct_3(k1_relat_1(A_48),k2_relat_1(A_48)),A_48) = k1_relat_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( v1_finset_1(k9_relat_1(A_11,B_12))
      | ~ v1_finset_1(B_12)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_152,plain,(
    ! [A_48] :
      ( v1_finset_1(k1_relat_1(A_48))
      | ~ v1_finset_1(A_48)
      | ~ v1_funct_1(k7_funct_3(k1_relat_1(A_48),k2_relat_1(A_48)))
      | ~ v1_relat_1(k7_funct_3(k1_relat_1(A_48),k2_relat_1(A_48)))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_16])).

tff(c_160,plain,(
    ! [A_49] :
      ( v1_finset_1(k1_relat_1(A_49))
      | ~ v1_finset_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_152])).

tff(c_166,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_160,c_40])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_41,c_166])).

tff(c_172,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_173,plain,(
    v1_finset_1(k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_236,plain,(
    ! [A_64,B_65] :
      ( v1_finset_1(k9_relat_1(A_64,B_65))
      | ~ v1_finset_1(B_65)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_266,plain,(
    ! [A_72] :
      ( v1_finset_1(k2_relat_1(A_72))
      | ~ v1_finset_1(k1_relat_1(A_72))
      | ~ v1_funct_1(A_72)
      | ~ v1_relat_1(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_236])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(k2_zfmisc_1(A_13,B_14))
      | ~ v1_finset_1(B_14)
      | ~ v1_finset_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197,plain,(
    ! [A_59] :
      ( k3_xboole_0(A_59,k2_zfmisc_1(k1_relat_1(A_59),k2_relat_1(A_59))) = A_59
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_finset_1(k3_xboole_0(A_9,B_10))
      | ~ v1_finset_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    ! [A_68] :
      ( v1_finset_1(A_68)
      | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(A_68),k2_relat_1(A_68)))
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_14])).

tff(c_245,plain,(
    ! [A_68] :
      ( v1_finset_1(A_68)
      | ~ v1_relat_1(A_68)
      | ~ v1_finset_1(k2_relat_1(A_68))
      | ~ v1_finset_1(k1_relat_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_18,c_241])).

tff(c_271,plain,(
    ! [A_73] :
      ( v1_finset_1(A_73)
      | ~ v1_finset_1(k1_relat_1(A_73))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_266,c_245])).

tff(c_280,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_173,c_271])).

tff(c_285,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_280])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:30:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.27  %$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k9_funct_3 > k7_relat_1 > k7_funct_3 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.27  tff(k7_funct_3, type, k7_funct_3: ($i * $i) > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.27  tff(k9_funct_3, type, k9_funct_3: ($i * $i) > $i).
% 2.23/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.23/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.27  
% 2.23/1.28  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_finset_1(k1_relat_1(A)) <=> v1_finset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_finset_1)).
% 2.23/1.28  tff(f_45, axiom, (![A, B]: (v1_relat_1(k7_funct_3(A, B)) & v1_funct_1(k7_funct_3(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_3)).
% 2.23/1.28  tff(f_65, axiom, (![A, B]: (k9_funct_3(A, B) = k7_funct_3(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_funct_3)).
% 2.23/1.28  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (k9_relat_1(k9_funct_3(k1_relat_1(A), k2_relat_1(A)), A) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_funct_3)).
% 2.23/1.28  tff(f_57, axiom, (![A, B]: (((v1_relat_1(A) & v1_funct_1(A)) & v1_finset_1(B)) => v1_finset_1(k9_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_finset_1)).
% 2.23/1.28  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.23/1.28  tff(f_63, axiom, (![A, B]: ((v1_finset_1(A) & v1_finset_1(B)) => v1_finset_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_finset_1)).
% 2.23/1.28  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.23/1.28  tff(f_49, axiom, (![A, B]: (v1_finset_1(B) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_finset_1)).
% 2.23/1.28  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.23/1.28  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.23/1.28  tff(c_30, plain, (~v1_finset_1('#skF_1') | ~v1_finset_1(k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.23/1.28  tff(c_40, plain, (~v1_finset_1(k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.23/1.28  tff(c_36, plain, (v1_finset_1(k1_relat_1('#skF_1')) | v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.23/1.28  tff(c_41, plain, (v1_finset_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_36])).
% 2.23/1.28  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_funct_3(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.28  tff(c_12, plain, (![A_7, B_8]: (v1_funct_1(k7_funct_3(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.28  tff(c_20, plain, (![A_15, B_16]: (k9_funct_3(A_15, B_16)=k7_funct_3(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.28  tff(c_22, plain, (![A_17]: (k9_relat_1(k9_funct_3(k1_relat_1(A_17), k2_relat_1(A_17)), A_17)=k1_relat_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.28  tff(c_146, plain, (![A_48]: (k9_relat_1(k7_funct_3(k1_relat_1(A_48), k2_relat_1(A_48)), A_48)=k1_relat_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.23/1.28  tff(c_16, plain, (![A_11, B_12]: (v1_finset_1(k9_relat_1(A_11, B_12)) | ~v1_finset_1(B_12) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.28  tff(c_152, plain, (![A_48]: (v1_finset_1(k1_relat_1(A_48)) | ~v1_finset_1(A_48) | ~v1_funct_1(k7_funct_3(k1_relat_1(A_48), k2_relat_1(A_48))) | ~v1_relat_1(k7_funct_3(k1_relat_1(A_48), k2_relat_1(A_48))) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_146, c_16])).
% 2.23/1.28  tff(c_160, plain, (![A_49]: (v1_finset_1(k1_relat_1(A_49)) | ~v1_finset_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_152])).
% 2.23/1.28  tff(c_166, plain, (~v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_160, c_40])).
% 2.23/1.28  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_41, c_166])).
% 2.23/1.28  tff(c_172, plain, (~v1_finset_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.23/1.28  tff(c_173, plain, (v1_finset_1(k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_30])).
% 2.23/1.28  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.28  tff(c_236, plain, (![A_64, B_65]: (v1_finset_1(k9_relat_1(A_64, B_65)) | ~v1_finset_1(B_65) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.28  tff(c_266, plain, (![A_72]: (v1_finset_1(k2_relat_1(A_72)) | ~v1_finset_1(k1_relat_1(A_72)) | ~v1_funct_1(A_72) | ~v1_relat_1(A_72) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_4, c_236])).
% 2.23/1.28  tff(c_18, plain, (![A_13, B_14]: (v1_finset_1(k2_zfmisc_1(A_13, B_14)) | ~v1_finset_1(B_14) | ~v1_finset_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.28  tff(c_197, plain, (![A_59]: (k3_xboole_0(A_59, k2_zfmisc_1(k1_relat_1(A_59), k2_relat_1(A_59)))=A_59 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.28  tff(c_14, plain, (![A_9, B_10]: (v1_finset_1(k3_xboole_0(A_9, B_10)) | ~v1_finset_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.28  tff(c_241, plain, (![A_68]: (v1_finset_1(A_68) | ~v1_finset_1(k2_zfmisc_1(k1_relat_1(A_68), k2_relat_1(A_68))) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_197, c_14])).
% 2.23/1.28  tff(c_245, plain, (![A_68]: (v1_finset_1(A_68) | ~v1_relat_1(A_68) | ~v1_finset_1(k2_relat_1(A_68)) | ~v1_finset_1(k1_relat_1(A_68)))), inference(resolution, [status(thm)], [c_18, c_241])).
% 2.23/1.28  tff(c_271, plain, (![A_73]: (v1_finset_1(A_73) | ~v1_finset_1(k1_relat_1(A_73)) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_266, c_245])).
% 2.23/1.28  tff(c_280, plain, (v1_finset_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_173, c_271])).
% 2.23/1.28  tff(c_285, plain, (v1_finset_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_280])).
% 2.23/1.28  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_285])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 54
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 1
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 0
% 2.23/1.28  #Demod        : 9
% 2.23/1.28  #Tautology    : 28
% 2.23/1.28  #SimpNegUnit  : 3
% 2.23/1.28  #BackRed      : 0
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.29  #Strategies tried      : 1
% 2.23/1.29  
% 2.23/1.29  Timing (in seconds)
% 2.23/1.29  ----------------------
% 2.23/1.29  Preprocessing        : 0.30
% 2.23/1.29  Parsing              : 0.16
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.20
% 2.23/1.29  Inferencing          : 0.09
% 2.23/1.29  Reduction            : 0.05
% 2.23/1.29  Demodulation         : 0.04
% 2.23/1.29  BG Simplification    : 0.01
% 2.23/1.29  Subsumption          : 0.02
% 2.23/1.29  Abstraction          : 0.01
% 2.23/1.29  MUC search           : 0.00
% 2.23/1.29  Cooper               : 0.00
% 2.23/1.29  Total                : 0.52
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
