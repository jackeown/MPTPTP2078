%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   65 ( 123 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [B_16,A_17] :
      ( v1_relat_1(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_41])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_46])).

tff(c_58,plain,(
    ! [B_28,A_29,C_30] :
      ( k1_xboole_0 = B_28
      | k1_relset_1(A_29,B_28,C_30) = A_29
      | ~ v1_funct_2(C_30,A_29,B_28)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_29,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_50,c_61])).

tff(c_65,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_64])).

tff(c_83,plain,(
    ! [B_34,A_35] :
      ( k1_funct_1(k2_funct_1(B_34),k1_funct_1(B_34,A_35)) = A_35
      | ~ r2_hidden(A_35,k1_relat_1(B_34))
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_24])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_30,c_28,c_65,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.13  
% 1.74/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.74/1.13  
% 1.74/1.13  %Foreground sorts:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Background operators:
% 1.74/1.13  
% 1.74/1.13  
% 1.74/1.13  %Foreground operators:
% 1.74/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.74/1.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.74/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.74/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.13  
% 1.74/1.14  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.74/1.14  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 1.74/1.14  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.74/1.14  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.74/1.14  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.74/1.14  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 1.74/1.14  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.74/1.14  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_38, plain, (![B_16, A_17]: (v1_relat_1(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_17)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.14  tff(c_41, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 1.74/1.14  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_41])).
% 1.74/1.14  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_30, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_28, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_46, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.14  tff(c_50, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_46])).
% 1.74/1.14  tff(c_58, plain, (![B_28, A_29, C_30]: (k1_xboole_0=B_28 | k1_relset_1(A_29, B_28, C_30)=A_29 | ~v1_funct_2(C_30, A_29, B_28) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_29, B_28))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.14  tff(c_61, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_58])).
% 1.74/1.14  tff(c_64, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_50, c_61])).
% 1.74/1.14  tff(c_65, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_26, c_64])).
% 1.74/1.14  tff(c_83, plain, (![B_34, A_35]: (k1_funct_1(k2_funct_1(B_34), k1_funct_1(B_34, A_35))=A_35 | ~r2_hidden(A_35, k1_relat_1(B_34)) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.14  tff(c_24, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.74/1.14  tff(c_92, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_83, c_24])).
% 1.74/1.14  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_30, c_28, c_65, c_92])).
% 1.74/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  Inference rules
% 1.74/1.14  ----------------------
% 1.74/1.14  #Ref     : 0
% 1.74/1.14  #Sup     : 15
% 1.74/1.14  #Fact    : 0
% 1.74/1.14  #Define  : 0
% 1.74/1.14  #Split   : 0
% 1.74/1.14  #Chain   : 0
% 1.74/1.14  #Close   : 0
% 1.74/1.14  
% 1.74/1.14  Ordering : KBO
% 1.74/1.14  
% 1.74/1.14  Simplification rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Subsume      : 0
% 1.74/1.15  #Demod        : 11
% 1.74/1.15  #Tautology    : 8
% 1.74/1.15  #SimpNegUnit  : 2
% 1.74/1.15  #BackRed      : 1
% 1.74/1.15  
% 1.74/1.15  #Partial instantiations: 0
% 1.74/1.15  #Strategies tried      : 1
% 1.74/1.15  
% 1.74/1.15  Timing (in seconds)
% 1.74/1.15  ----------------------
% 1.74/1.15  Preprocessing        : 0.29
% 1.74/1.15  Parsing              : 0.15
% 1.74/1.15  CNF conversion       : 0.02
% 1.74/1.15  Main loop            : 0.12
% 1.74/1.15  Inferencing          : 0.04
% 1.74/1.15  Reduction            : 0.04
% 1.74/1.15  Demodulation         : 0.03
% 1.74/1.15  BG Simplification    : 0.01
% 1.74/1.15  Subsumption          : 0.02
% 1.74/1.15  Abstraction          : 0.01
% 1.74/1.15  MUC search           : 0.00
% 1.74/1.15  Cooper               : 0.00
% 1.74/1.15  Total                : 0.44
% 1.74/1.15  Index Insertion      : 0.00
% 1.74/1.15  Index Deletion       : 0.00
% 1.74/1.15  Index Matching       : 0.00
% 1.74/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
