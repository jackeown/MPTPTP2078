%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   51 (  56 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  78 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
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

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ! [A_29,B_30] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_29,B_30)),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_29] : k2_relat_1(k2_zfmisc_1(A_29,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,(
    ! [A_40,B_41] :
      ( k2_relat_1(k2_zfmisc_1(A_40,B_41)) != k1_xboole_0
      | k2_zfmisc_1(A_40,B_41) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_87])).

tff(c_156,plain,(
    ! [A_45] : k2_zfmisc_1(A_45,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_148])).

tff(c_6,plain,(
    ! [A_2,B_3] : ~ r2_hidden(A_2,k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [A_45] : ~ r2_hidden(A_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_6])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_32,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_135,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),k1_relat_1(B_36))
      | v5_funct_1(B_36,A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_138,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_35)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_140,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_45,c_138])).

tff(c_185,plain,(
    ! [A_47] :
      ( v5_funct_1(k1_xboole_0,A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_140])).

tff(c_34,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_188,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_185,c_34])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.25  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.12/1.25  
% 2.12/1.25  %Foreground sorts:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Background operators:
% 2.12/1.25  
% 2.12/1.25  
% 2.12/1.25  %Foreground operators:
% 2.12/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.25  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.12/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.25  
% 2.12/1.26  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.12/1.26  tff(f_37, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 2.12/1.26  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.12/1.26  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.12/1.26  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.12/1.26  tff(f_33, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.12/1.26  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.12/1.26  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.12/1.26  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.26  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.12/1.26  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.26  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.26  tff(c_66, plain, (![A_29, B_30]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_29, B_30)), B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.26  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.12/1.26  tff(c_71, plain, (![A_29]: (k2_relat_1(k2_zfmisc_1(A_29, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_4])).
% 2.12/1.26  tff(c_8, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.26  tff(c_87, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.26  tff(c_148, plain, (![A_40, B_41]: (k2_relat_1(k2_zfmisc_1(A_40, B_41))!=k1_xboole_0 | k2_zfmisc_1(A_40, B_41)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_87])).
% 2.12/1.26  tff(c_156, plain, (![A_45]: (k2_zfmisc_1(A_45, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_71, c_148])).
% 2.12/1.26  tff(c_6, plain, (![A_2, B_3]: (~r2_hidden(A_2, k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.26  tff(c_170, plain, (![A_45]: (~r2_hidden(A_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_6])).
% 2.12/1.26  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.26  tff(c_30, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.26  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_30])).
% 2.12/1.26  tff(c_32, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.12/1.26  tff(c_45, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_32])).
% 2.12/1.26  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.12/1.26  tff(c_135, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), k1_relat_1(B_36)) | v5_funct_1(B_36, A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.26  tff(c_138, plain, (![A_35]: (r2_hidden('#skF_1'(A_35, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_35) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_14, c_135])).
% 2.12/1.26  tff(c_140, plain, (![A_35]: (r2_hidden('#skF_1'(A_35, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_45, c_138])).
% 2.12/1.26  tff(c_185, plain, (![A_47]: (v5_funct_1(k1_xboole_0, A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(negUnitSimplification, [status(thm)], [c_170, c_140])).
% 2.12/1.26  tff(c_34, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.26  tff(c_188, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_185, c_34])).
% 2.12/1.26  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_188])).
% 2.12/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  Inference rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Ref     : 0
% 2.12/1.26  #Sup     : 34
% 2.12/1.26  #Fact    : 0
% 2.12/1.26  #Define  : 0
% 2.12/1.26  #Split   : 2
% 2.12/1.26  #Chain   : 0
% 2.12/1.26  #Close   : 0
% 2.12/1.26  
% 2.12/1.26  Ordering : KBO
% 2.12/1.26  
% 2.12/1.26  Simplification rules
% 2.12/1.26  ----------------------
% 2.12/1.26  #Subsume      : 0
% 2.12/1.26  #Demod        : 20
% 2.12/1.26  #Tautology    : 21
% 2.12/1.26  #SimpNegUnit  : 1
% 2.12/1.26  #BackRed      : 1
% 2.12/1.26  
% 2.12/1.26  #Partial instantiations: 0
% 2.12/1.26  #Strategies tried      : 1
% 2.12/1.26  
% 2.12/1.26  Timing (in seconds)
% 2.12/1.26  ----------------------
% 2.12/1.26  Preprocessing        : 0.29
% 2.12/1.26  Parsing              : 0.16
% 2.12/1.26  CNF conversion       : 0.02
% 2.12/1.26  Main loop            : 0.17
% 2.12/1.26  Inferencing          : 0.07
% 2.12/1.26  Reduction            : 0.05
% 2.12/1.26  Demodulation         : 0.04
% 2.12/1.26  BG Simplification    : 0.01
% 2.12/1.26  Subsumption          : 0.03
% 2.12/1.26  Abstraction          : 0.01
% 2.12/1.26  MUC search           : 0.00
% 2.12/1.26  Cooper               : 0.00
% 2.12/1.26  Total                : 0.49
% 2.12/1.26  Index Insertion      : 0.00
% 2.12/1.26  Index Deletion       : 0.00
% 2.12/1.26  Index Matching       : 0.00
% 2.12/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
