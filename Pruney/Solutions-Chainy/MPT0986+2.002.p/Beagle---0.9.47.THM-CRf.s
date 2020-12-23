%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 115 expanded)
%              Number of leaves         :   31 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 326 expanded)
%              Number of equality atoms :   27 (  94 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_65,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_69,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_65])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_71])).

tff(c_83,plain,(
    ! [B_43,A_44,C_45] :
      ( k1_xboole_0 = B_43
      | k1_relset_1(A_44,B_43,C_45) = A_44
      | ~ v1_funct_2(C_45,A_44,B_43)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_86,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_89,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_75,c_86])).

tff(c_90,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_89])).

tff(c_128,plain,(
    ! [A_54,D_55] :
      ( k1_funct_1(k2_funct_1(A_54),k1_funct_1(A_54,D_55)) = D_55
      | ~ r2_hidden(D_55,k1_relat_1(A_54))
      | ~ v1_funct_1(k2_funct_1(A_54))
      | ~ v1_relat_1(k2_funct_1(A_54))
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    k1_funct_1(k2_funct_1('#skF_8'),k1_funct_1('#skF_8','#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_140,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_50])).

tff(c_150,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_62,c_56,c_54,c_90,c_140])).

tff(c_152,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_155,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_62,c_155])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_164,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_62,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.23  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.26/1.23  
% 2.26/1.23  %Foreground sorts:
% 2.26/1.23  
% 2.26/1.23  
% 2.26/1.23  %Background operators:
% 2.26/1.23  
% 2.26/1.23  
% 2.26/1.23  %Foreground operators:
% 2.26/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.26/1.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.26/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.23  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.26/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.23  tff('#skF_8', type, '#skF_8': $i).
% 2.26/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.26/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.23  
% 2.26/1.24  tff(f_106, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.26/1.24  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.24  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.26/1.24  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.26/1.24  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.26/1.24  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.26/1.24  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_65, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.26/1.24  tff(c_69, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_65])).
% 2.26/1.24  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.24  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.24  tff(c_56, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_54, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_71, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.26/1.24  tff(c_75, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_71])).
% 2.26/1.24  tff(c_83, plain, (![B_43, A_44, C_45]: (k1_xboole_0=B_43 | k1_relset_1(A_44, B_43, C_45)=A_44 | ~v1_funct_2(C_45, A_44, B_43) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.26/1.24  tff(c_86, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_83])).
% 2.26/1.24  tff(c_89, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_75, c_86])).
% 2.26/1.24  tff(c_90, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_52, c_89])).
% 2.26/1.24  tff(c_128, plain, (![A_54, D_55]: (k1_funct_1(k2_funct_1(A_54), k1_funct_1(A_54, D_55))=D_55 | ~r2_hidden(D_55, k1_relat_1(A_54)) | ~v1_funct_1(k2_funct_1(A_54)) | ~v1_relat_1(k2_funct_1(A_54)) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.24  tff(c_50, plain, (k1_funct_1(k2_funct_1('#skF_8'), k1_funct_1('#skF_8', '#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.26/1.24  tff(c_140, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_128, c_50])).
% 2.26/1.24  tff(c_150, plain, (~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_62, c_56, c_54, c_90, c_140])).
% 2.26/1.24  tff(c_152, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_150])).
% 2.26/1.24  tff(c_155, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4, c_152])).
% 2.26/1.24  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_62, c_155])).
% 2.26/1.24  tff(c_160, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_150])).
% 2.26/1.24  tff(c_164, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_2, c_160])).
% 2.26/1.24  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_62, c_164])).
% 2.26/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.24  
% 2.26/1.24  Inference rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Ref     : 0
% 2.26/1.24  #Sup     : 22
% 2.26/1.24  #Fact    : 0
% 2.26/1.24  #Define  : 0
% 2.26/1.24  #Split   : 1
% 2.26/1.24  #Chain   : 0
% 2.26/1.24  #Close   : 0
% 2.26/1.24  
% 2.26/1.24  Ordering : KBO
% 2.26/1.24  
% 2.26/1.24  Simplification rules
% 2.26/1.24  ----------------------
% 2.26/1.24  #Subsume      : 2
% 2.26/1.24  #Demod        : 14
% 2.26/1.24  #Tautology    : 11
% 2.26/1.24  #SimpNegUnit  : 2
% 2.26/1.24  #BackRed      : 1
% 2.26/1.24  
% 2.26/1.24  #Partial instantiations: 0
% 2.26/1.24  #Strategies tried      : 1
% 2.26/1.24  
% 2.26/1.24  Timing (in seconds)
% 2.26/1.24  ----------------------
% 2.26/1.24  Preprocessing        : 0.33
% 2.26/1.24  Parsing              : 0.16
% 2.26/1.24  CNF conversion       : 0.02
% 2.26/1.24  Main loop            : 0.16
% 2.26/1.25  Inferencing          : 0.05
% 2.26/1.25  Reduction            : 0.05
% 2.26/1.25  Demodulation         : 0.04
% 2.26/1.25  BG Simplification    : 0.02
% 2.26/1.25  Subsumption          : 0.04
% 2.26/1.25  Abstraction          : 0.01
% 2.26/1.25  MUC search           : 0.00
% 2.26/1.25  Cooper               : 0.00
% 2.26/1.25  Total                : 0.52
% 2.26/1.25  Index Insertion      : 0.00
% 2.26/1.25  Index Deletion       : 0.00
% 2.26/1.25  Index Matching       : 0.00
% 2.26/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
