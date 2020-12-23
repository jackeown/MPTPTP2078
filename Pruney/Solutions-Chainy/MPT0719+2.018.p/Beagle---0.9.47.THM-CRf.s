%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 (  80 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
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

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [A_28,B_29] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_28,B_29)),B_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_61,plain,(
    ! [A_28] : k2_relat_1(k2_zfmisc_1(A_28,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_10,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [A_32] :
      ( k2_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    ! [A_35,B_36] :
      ( k2_relat_1(k2_zfmisc_1(A_35,B_36)) != k1_xboole_0
      | k2_zfmisc_1(A_35,B_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_119,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_112])).

tff(c_6,plain,(
    ! [A_2,B_3] : ~ r2_hidden(A_2,k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_49,plain,(
    ! [A_24] :
      ( v1_relat_1(A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_43,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),k1_relat_1(B_39))
      | v5_funct_1(B_39,A_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_1'(A_38,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_38)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_146])).

tff(c_151,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_1'(A_38,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_47,c_149])).

tff(c_154,plain,(
    ! [A_41] :
      ( v5_funct_1(k1_xboole_0,A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_151])).

tff(c_30,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_157,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_30])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.34  
% 2.16/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.34  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.34  
% 2.16/1.34  %Foreground sorts:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Background operators:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Foreground operators:
% 2.16/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.34  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.16/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.34  
% 2.16/1.35  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.16/1.35  tff(f_41, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 2.16/1.35  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.16/1.35  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.16/1.35  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.16/1.35  tff(f_33, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.16/1.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.35  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.16/1.35  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.16/1.35  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.16/1.35  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.16/1.35  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_32, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_56, plain, (![A_28, B_29]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_28, B_29)), B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.16/1.35  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.16/1.35  tff(c_61, plain, (![A_28]: (k2_relat_1(k2_zfmisc_1(A_28, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_4])).
% 2.16/1.35  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.35  tff(c_94, plain, (![A_32]: (k2_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.35  tff(c_112, plain, (![A_35, B_36]: (k2_relat_1(k2_zfmisc_1(A_35, B_36))!=k1_xboole_0 | k2_zfmisc_1(A_35, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.16/1.35  tff(c_119, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_112])).
% 2.16/1.35  tff(c_6, plain, (![A_2, B_3]: (~r2_hidden(A_2, k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.35  tff(c_133, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119, c_6])).
% 2.16/1.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.16/1.35  tff(c_49, plain, (![A_24]: (v1_relat_1(A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.35  tff(c_53, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.16/1.35  tff(c_43, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.16/1.35  tff(c_47, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 2.16/1.35  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.35  tff(c_146, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), k1_relat_1(B_39)) | v5_funct_1(B_39, A_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.16/1.35  tff(c_149, plain, (![A_38]: (r2_hidden('#skF_1'(A_38, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_38) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_16, c_146])).
% 2.16/1.35  tff(c_151, plain, (![A_38]: (r2_hidden('#skF_1'(A_38, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_47, c_149])).
% 2.16/1.35  tff(c_154, plain, (![A_41]: (v5_funct_1(k1_xboole_0, A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(negUnitSimplification, [status(thm)], [c_133, c_151])).
% 2.16/1.35  tff(c_30, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_157, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_154, c_30])).
% 2.16/1.35  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_157])).
% 2.16/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.35  
% 2.16/1.35  Inference rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Ref     : 0
% 2.16/1.35  #Sup     : 27
% 2.16/1.35  #Fact    : 0
% 2.16/1.35  #Define  : 0
% 2.16/1.35  #Split   : 2
% 2.16/1.35  #Chain   : 0
% 2.16/1.35  #Close   : 0
% 2.16/1.35  
% 2.16/1.35  Ordering : KBO
% 2.16/1.35  
% 2.16/1.35  Simplification rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Subsume      : 0
% 2.16/1.35  #Demod        : 15
% 2.16/1.35  #Tautology    : 16
% 2.16/1.35  #SimpNegUnit  : 1
% 2.16/1.35  #BackRed      : 1
% 2.16/1.35  
% 2.16/1.35  #Partial instantiations: 0
% 2.16/1.35  #Strategies tried      : 1
% 2.16/1.35  
% 2.16/1.35  Timing (in seconds)
% 2.16/1.35  ----------------------
% 2.16/1.36  Preprocessing        : 0.36
% 2.16/1.36  Parsing              : 0.22
% 2.16/1.36  CNF conversion       : 0.02
% 2.16/1.36  Main loop            : 0.18
% 2.16/1.36  Inferencing          : 0.07
% 2.16/1.36  Reduction            : 0.05
% 2.16/1.36  Demodulation         : 0.04
% 2.16/1.36  BG Simplification    : 0.01
% 2.16/1.36  Subsumption          : 0.03
% 2.16/1.36  Abstraction          : 0.01
% 2.16/1.36  MUC search           : 0.00
% 2.16/1.36  Cooper               : 0.00
% 2.16/1.36  Total                : 0.58
% 2.16/1.36  Index Insertion      : 0.00
% 2.16/1.36  Index Deletion       : 0.00
% 2.16/1.36  Index Matching       : 0.00
% 2.16/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
