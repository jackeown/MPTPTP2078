%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:05 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   57 (  96 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 154 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_33,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_39,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_115,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_115])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v5_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [C_34,A_35,B_36] :
      ( v4_relat_1(C_34,A_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_49,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_41,A_7,B_8] :
      ( r1_tarski(A_41,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_41,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_20,plain,(
    ! [A_19] :
      ( k2_xboole_0(k1_relat_1(A_19),k2_relat_1(A_19)) = k3_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_tarski(k2_xboole_0(A_61,C_62),B_63)
      | ~ r1_tarski(C_62,B_63)
      | ~ r1_tarski(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_427,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k3_relat_1(A_122),B_123)
      | ~ r1_tarski(k2_relat_1(A_122),B_123)
      | ~ r1_tarski(k1_relat_1(A_122),B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_448,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_427,c_28])).

tff(c_462,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_448])).

tff(c_470,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_462])).

tff(c_483,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_470])).

tff(c_487,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_483])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_49,c_487])).

tff(c_492,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_462])).

tff(c_507,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_492])).

tff(c_556,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_507])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_119,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.39  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.39  
% 2.77/1.39  %Foreground sorts:
% 2.77/1.39  
% 2.77/1.39  
% 2.77/1.39  %Background operators:
% 2.77/1.39  
% 2.77/1.39  
% 2.77/1.39  %Foreground operators:
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.39  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.77/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.39  
% 2.77/1.41  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.41  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 2.77/1.41  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.41  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.41  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.77/1.41  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.77/1.41  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.41  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.77/1.41  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.77/1.41  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.77/1.41  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.77/1.41  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.41  tff(c_33, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.77/1.41  tff(c_36, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.77/1.41  tff(c_39, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36])).
% 2.77/1.41  tff(c_115, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.41  tff(c_119, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_115])).
% 2.77/1.41  tff(c_18, plain, (![B_18, A_17]: (r1_tarski(k2_relat_1(B_18), A_17) | ~v5_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.41  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.41  tff(c_45, plain, (![C_34, A_35, B_36]: (v4_relat_1(C_34, A_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.41  tff(c_49, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.77/1.41  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.41  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.41  tff(c_62, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.41  tff(c_68, plain, (![A_41, A_7, B_8]: (r1_tarski(A_41, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_41, A_7))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.77/1.41  tff(c_20, plain, (![A_19]: (k2_xboole_0(k1_relat_1(A_19), k2_relat_1(A_19))=k3_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.77/1.41  tff(c_150, plain, (![A_61, C_62, B_63]: (r1_tarski(k2_xboole_0(A_61, C_62), B_63) | ~r1_tarski(C_62, B_63) | ~r1_tarski(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.41  tff(c_427, plain, (![A_122, B_123]: (r1_tarski(k3_relat_1(A_122), B_123) | ~r1_tarski(k2_relat_1(A_122), B_123) | ~r1_tarski(k1_relat_1(A_122), B_123) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_20, c_150])).
% 2.77/1.41  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.41  tff(c_448, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_427, c_28])).
% 2.77/1.41  tff(c_462, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_448])).
% 2.77/1.41  tff(c_470, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_462])).
% 2.77/1.41  tff(c_483, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_68, c_470])).
% 2.77/1.41  tff(c_487, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_483])).
% 2.77/1.41  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_49, c_487])).
% 2.77/1.41  tff(c_492, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_462])).
% 2.77/1.41  tff(c_507, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2, c_492])).
% 2.77/1.41  tff(c_556, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_507])).
% 2.77/1.41  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_119, c_556])).
% 2.77/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  Inference rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Ref     : 0
% 2.77/1.41  #Sup     : 130
% 2.77/1.41  #Fact    : 0
% 2.77/1.41  #Define  : 0
% 2.77/1.41  #Split   : 2
% 2.77/1.41  #Chain   : 0
% 2.77/1.41  #Close   : 0
% 2.77/1.41  
% 2.77/1.41  Ordering : KBO
% 2.77/1.41  
% 2.77/1.41  Simplification rules
% 2.77/1.41  ----------------------
% 2.77/1.41  #Subsume      : 7
% 2.77/1.41  #Demod        : 12
% 2.77/1.41  #Tautology    : 5
% 2.77/1.41  #SimpNegUnit  : 0
% 2.77/1.41  #BackRed      : 0
% 2.77/1.41  
% 2.77/1.41  #Partial instantiations: 0
% 2.77/1.41  #Strategies tried      : 1
% 2.77/1.41  
% 2.77/1.41  Timing (in seconds)
% 2.77/1.41  ----------------------
% 2.77/1.41  Preprocessing        : 0.29
% 2.77/1.41  Parsing              : 0.16
% 2.77/1.41  CNF conversion       : 0.02
% 2.77/1.41  Main loop            : 0.36
% 2.77/1.41  Inferencing          : 0.14
% 2.77/1.41  Reduction            : 0.09
% 2.77/1.41  Demodulation         : 0.06
% 2.77/1.41  BG Simplification    : 0.02
% 2.77/1.41  Subsumption          : 0.08
% 2.77/1.41  Abstraction          : 0.01
% 2.77/1.41  MUC search           : 0.00
% 2.77/1.41  Cooper               : 0.00
% 2.77/1.41  Total                : 0.67
% 2.77/1.41  Index Insertion      : 0.00
% 2.77/1.41  Index Deletion       : 0.00
% 2.77/1.41  Index Matching       : 0.00
% 2.77/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
