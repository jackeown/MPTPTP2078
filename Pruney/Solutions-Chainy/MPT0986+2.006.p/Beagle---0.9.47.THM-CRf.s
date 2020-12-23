%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 127 expanded)
%              Number of leaves         :   32 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 350 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_74,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_68,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_71])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_75,plain,(
    ! [A_36,B_37,C_38] :
      ( k1_relset_1(A_36,B_37,C_38) = k1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_79,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_75])).

tff(c_88,plain,(
    ! [B_46,A_47,C_48] :
      ( k1_xboole_0 = B_46
      | k1_relset_1(A_47,B_46,C_48) = A_47
      | ~ v1_funct_2(C_48,A_47,B_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_47,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_94,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_79,c_91])).

tff(c_95,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_94])).

tff(c_133,plain,(
    ! [A_57,D_58] :
      ( k1_funct_1(k2_funct_1(A_57),k1_funct_1(A_57,D_58)) = D_58
      | ~ r2_hidden(D_58,k1_relat_1(A_57))
      | ~ v1_funct_1(k2_funct_1(A_57))
      | ~ v1_relat_1(k2_funct_1(A_57))
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    k1_funct_1(k2_funct_1('#skF_8'),k1_funct_1('#skF_8','#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_145,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_52])).

tff(c_155,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_58,c_56,c_95,c_145])).

tff(c_157,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_160,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_160])).

tff(c_165,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.26  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.32/1.26  
% 2.32/1.26  %Foreground sorts:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Background operators:
% 2.32/1.26  
% 2.32/1.26  
% 2.32/1.26  %Foreground operators:
% 2.32/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.26  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.32/1.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.32/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.32/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.32/1.26  tff('#skF_8', type, '#skF_8': $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.32/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.32/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.32/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.26  
% 2.32/1.27  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.32/1.27  tff(f_111, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.32/1.27  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.32/1.27  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.32/1.27  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.32/1.27  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.32/1.27  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.32/1.27  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.32/1.27  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_68, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.32/1.27  tff(c_71, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_68])).
% 2.32/1.27  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_71])).
% 2.32/1.27  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_6, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.32/1.27  tff(c_8, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.32/1.27  tff(c_58, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_75, plain, (![A_36, B_37, C_38]: (k1_relset_1(A_36, B_37, C_38)=k1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.32/1.27  tff(c_79, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_75])).
% 2.32/1.27  tff(c_88, plain, (![B_46, A_47, C_48]: (k1_xboole_0=B_46 | k1_relset_1(A_47, B_46, C_48)=A_47 | ~v1_funct_2(C_48, A_47, B_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_47, B_46))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.32/1.27  tff(c_91, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_88])).
% 2.32/1.27  tff(c_94, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_79, c_91])).
% 2.32/1.27  tff(c_95, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_94])).
% 2.32/1.27  tff(c_133, plain, (![A_57, D_58]: (k1_funct_1(k2_funct_1(A_57), k1_funct_1(A_57, D_58))=D_58 | ~r2_hidden(D_58, k1_relat_1(A_57)) | ~v1_funct_1(k2_funct_1(A_57)) | ~v1_relat_1(k2_funct_1(A_57)) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.27  tff(c_52, plain, (k1_funct_1(k2_funct_1('#skF_8'), k1_funct_1('#skF_8', '#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.32/1.27  tff(c_145, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_133, c_52])).
% 2.32/1.27  tff(c_155, plain, (~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_58, c_56, c_95, c_145])).
% 2.32/1.27  tff(c_157, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_155])).
% 2.32/1.27  tff(c_160, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_8, c_157])).
% 2.32/1.27  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_160])).
% 2.32/1.27  tff(c_165, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_155])).
% 2.32/1.27  tff(c_169, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6, c_165])).
% 2.32/1.27  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_169])).
% 2.32/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.27  
% 2.32/1.27  Inference rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Ref     : 0
% 2.32/1.27  #Sup     : 22
% 2.32/1.27  #Fact    : 0
% 2.32/1.27  #Define  : 0
% 2.32/1.27  #Split   : 1
% 2.32/1.27  #Chain   : 0
% 2.32/1.27  #Close   : 0
% 2.32/1.27  
% 2.32/1.27  Ordering : KBO
% 2.32/1.27  
% 2.32/1.27  Simplification rules
% 2.32/1.27  ----------------------
% 2.32/1.27  #Subsume      : 2
% 2.32/1.27  #Demod        : 15
% 2.32/1.27  #Tautology    : 11
% 2.32/1.27  #SimpNegUnit  : 2
% 2.32/1.27  #BackRed      : 1
% 2.32/1.27  
% 2.32/1.27  #Partial instantiations: 0
% 2.32/1.27  #Strategies tried      : 1
% 2.32/1.27  
% 2.32/1.27  Timing (in seconds)
% 2.32/1.27  ----------------------
% 2.32/1.27  Preprocessing        : 0.33
% 2.32/1.27  Parsing              : 0.16
% 2.32/1.27  CNF conversion       : 0.02
% 2.32/1.27  Main loop            : 0.18
% 2.32/1.27  Inferencing          : 0.05
% 2.32/1.27  Reduction            : 0.05
% 2.32/1.27  Demodulation         : 0.04
% 2.32/1.27  BG Simplification    : 0.02
% 2.32/1.27  Subsumption          : 0.04
% 2.32/1.28  Abstraction          : 0.01
% 2.32/1.28  MUC search           : 0.00
% 2.32/1.28  Cooper               : 0.00
% 2.32/1.28  Total                : 0.53
% 2.32/1.28  Index Insertion      : 0.00
% 2.32/1.28  Index Deletion       : 0.00
% 2.32/1.28  Index Matching       : 0.00
% 2.32/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
