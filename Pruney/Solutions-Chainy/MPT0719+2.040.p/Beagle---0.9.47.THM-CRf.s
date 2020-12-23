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

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 (  62 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 (  84 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_51,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
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
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_31] : r1_tarski('#skF_1'(A_31),A_31) ),
    inference(resolution,[status(thm)],[c_8,c_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_81,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_88,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_8])).

tff(c_14,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_88,c_14])).

tff(c_114,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_32,plain,(
    ! [A_20] : v1_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_45,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39),k1_relat_1(B_39))
      | v5_funct_1(B_39,A_38)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_127,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_38)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_129,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_45,c_127])).

tff(c_131,plain,(
    ! [A_40] :
      ( v5_funct_1(k1_xboole_0,A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_129])).

tff(c_34,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_134,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_34])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.29  
% 1.90/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.30  %$ v5_funct_1 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.90/1.30  
% 1.90/1.30  %Foreground sorts:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Background operators:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Foreground operators:
% 1.90/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.30  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.90/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.30  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.90/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.30  
% 2.05/1.31  tff(f_82, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.05/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.05/1.31  tff(f_36, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.05/1.31  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.31  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.05/1.31  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.05/1.31  tff(f_51, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.05/1.31  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.05/1.31  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.05/1.31  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.05/1.31  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.05/1.31  tff(c_8, plain, (![A_2]: (m1_subset_1('#skF_1'(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.05/1.31  tff(c_67, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.31  tff(c_76, plain, (![A_31]: (r1_tarski('#skF_1'(A_31), A_31))), inference(resolution, [status(thm)], [c_8, c_67])).
% 2.05/1.31  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.05/1.31  tff(c_81, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_4])).
% 2.05/1.31  tff(c_88, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_81, c_8])).
% 2.05/1.31  tff(c_14, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.05/1.31  tff(c_108, plain, (![A_6]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_88, c_14])).
% 2.05/1.31  tff(c_114, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_108])).
% 2.05/1.31  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.31  tff(c_30, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.31  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_30])).
% 2.05/1.31  tff(c_32, plain, (![A_20]: (v1_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.05/1.31  tff(c_45, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_32])).
% 2.05/1.31  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.05/1.31  tff(c_124, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39), k1_relat_1(B_39)) | v5_funct_1(B_39, A_38) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.31  tff(c_127, plain, (![A_38]: (r2_hidden('#skF_2'(A_38, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_38) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_18, c_124])).
% 2.05/1.31  tff(c_129, plain, (![A_38]: (r2_hidden('#skF_2'(A_38, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_45, c_127])).
% 2.05/1.31  tff(c_131, plain, (![A_40]: (v5_funct_1(k1_xboole_0, A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(negUnitSimplification, [status(thm)], [c_114, c_129])).
% 2.05/1.31  tff(c_34, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.05/1.31  tff(c_134, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_34])).
% 2.05/1.31  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_134])).
% 2.05/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.31  
% 2.05/1.31  Inference rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Ref     : 0
% 2.05/1.31  #Sup     : 25
% 2.05/1.31  #Fact    : 0
% 2.05/1.31  #Define  : 0
% 2.05/1.31  #Split   : 0
% 2.05/1.31  #Chain   : 0
% 2.05/1.31  #Close   : 0
% 2.05/1.31  
% 2.05/1.31  Ordering : KBO
% 2.05/1.31  
% 2.05/1.31  Simplification rules
% 2.05/1.31  ----------------------
% 2.05/1.31  #Subsume      : 1
% 2.05/1.31  #Demod        : 8
% 2.05/1.31  #Tautology    : 12
% 2.05/1.31  #SimpNegUnit  : 1
% 2.05/1.31  #BackRed      : 0
% 2.05/1.31  
% 2.05/1.31  #Partial instantiations: 0
% 2.05/1.31  #Strategies tried      : 1
% 2.05/1.31  
% 2.05/1.31  Timing (in seconds)
% 2.05/1.31  ----------------------
% 2.05/1.31  Preprocessing        : 0.33
% 2.05/1.31  Parsing              : 0.18
% 2.05/1.31  CNF conversion       : 0.02
% 2.05/1.31  Main loop            : 0.14
% 2.05/1.31  Inferencing          : 0.06
% 2.05/1.31  Reduction            : 0.04
% 2.05/1.31  Demodulation         : 0.03
% 2.05/1.31  BG Simplification    : 0.01
% 2.05/1.31  Subsumption          : 0.02
% 2.05/1.31  Abstraction          : 0.01
% 2.05/1.31  MUC search           : 0.00
% 2.05/1.31  Cooper               : 0.00
% 2.05/1.31  Total                : 0.50
% 2.05/1.31  Index Insertion      : 0.00
% 2.05/1.31  Index Deletion       : 0.00
% 2.05/1.31  Index Matching       : 0.00
% 2.05/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
