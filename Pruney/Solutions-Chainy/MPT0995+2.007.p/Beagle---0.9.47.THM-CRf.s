%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:50 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 161 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( ? [F] :
                  ( r2_hidden(F,A)
                  & r2_hidden(F,C)
                  & E = k1_funct_1(D,F) )
             => r2_hidden(E,k7_relset_1(A,B,D,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_50,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    r2_hidden('#skF_10','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_73,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_73])).

tff(c_100,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_100])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_77,c_103])).

tff(c_107,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_106])).

tff(c_48,plain,(
    k1_funct_1('#skF_8','#skF_10') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_125,plain,(
    ! [A_87,E_88,B_89] :
      ( r2_hidden(k1_funct_1(A_87,E_88),k9_relat_1(A_87,B_89))
      | ~ r2_hidden(E_88,B_89)
      | ~ r2_hidden(E_88,k1_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_128,plain,(
    ! [B_89] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_89))
      | ~ r2_hidden('#skF_10',B_89)
      | ~ r2_hidden('#skF_10',k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_125])).

tff(c_132,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_93))
      | ~ r2_hidden('#skF_10',B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60,c_52,c_107,c_128])).

tff(c_83,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k7_relset_1(A_70,B_71,C_72,D_73) = k9_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [D_73] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_73) = k9_relat_1('#skF_8',D_73) ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_46])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_132,c_88])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.25  tff('#skF_10', type, '#skF_10': $i).
% 2.17/1.25  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_9', type, '#skF_9': $i).
% 2.17/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.25  
% 2.26/1.26  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (~(B = k1_xboole_0) => (![E]: ((?[F]: ((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))) => r2_hidden(E, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_2)).
% 2.26/1.26  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.26/1.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.26/1.26  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.26/1.26  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.26/1.26  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.26/1.26  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.26/1.26  tff(c_50, plain, (r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.26/1.26  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_66, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.26  tff(c_69, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_66])).
% 2.26/1.26  tff(c_72, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_69])).
% 2.26/1.26  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_52, plain, (r2_hidden('#skF_10', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_73, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.26  tff(c_77, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_73])).
% 2.26/1.26  tff(c_100, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.26  tff(c_103, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_100])).
% 2.26/1.26  tff(c_106, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_77, c_103])).
% 2.26/1.26  tff(c_107, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_106])).
% 2.26/1.26  tff(c_48, plain, (k1_funct_1('#skF_8', '#skF_10')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_125, plain, (![A_87, E_88, B_89]: (r2_hidden(k1_funct_1(A_87, E_88), k9_relat_1(A_87, B_89)) | ~r2_hidden(E_88, B_89) | ~r2_hidden(E_88, k1_relat_1(A_87)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.26  tff(c_128, plain, (![B_89]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_89)) | ~r2_hidden('#skF_10', B_89) | ~r2_hidden('#skF_10', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_125])).
% 2.26/1.26  tff(c_132, plain, (![B_93]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_93)) | ~r2_hidden('#skF_10', B_93))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_60, c_52, c_107, c_128])).
% 2.26/1.26  tff(c_83, plain, (![A_70, B_71, C_72, D_73]: (k7_relset_1(A_70, B_71, C_72, D_73)=k9_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.26  tff(c_86, plain, (![D_73]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_73)=k9_relat_1('#skF_8', D_73))), inference(resolution, [status(thm)], [c_56, c_83])).
% 2.26/1.26  tff(c_46, plain, (~r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.26  tff(c_88, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_46])).
% 2.26/1.26  tff(c_135, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_132, c_88])).
% 2.26/1.26  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_135])).
% 2.26/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.26  
% 2.26/1.26  Inference rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Ref     : 0
% 2.26/1.26  #Sup     : 17
% 2.26/1.26  #Fact    : 0
% 2.26/1.26  #Define  : 0
% 2.26/1.26  #Split   : 0
% 2.26/1.26  #Chain   : 0
% 2.26/1.26  #Close   : 0
% 2.26/1.26  
% 2.26/1.26  Ordering : KBO
% 2.26/1.26  
% 2.26/1.26  Simplification rules
% 2.26/1.26  ----------------------
% 2.26/1.26  #Subsume      : 0
% 2.26/1.26  #Demod        : 12
% 2.26/1.26  #Tautology    : 11
% 2.26/1.26  #SimpNegUnit  : 2
% 2.26/1.26  #BackRed      : 2
% 2.26/1.26  
% 2.26/1.26  #Partial instantiations: 0
% 2.26/1.26  #Strategies tried      : 1
% 2.26/1.26  
% 2.26/1.26  Timing (in seconds)
% 2.26/1.26  ----------------------
% 2.26/1.27  Preprocessing        : 0.35
% 2.26/1.27  Parsing              : 0.17
% 2.26/1.27  CNF conversion       : 0.03
% 2.26/1.27  Main loop            : 0.16
% 2.26/1.27  Inferencing          : 0.05
% 2.26/1.27  Reduction            : 0.05
% 2.26/1.27  Demodulation         : 0.04
% 2.26/1.27  BG Simplification    : 0.02
% 2.26/1.27  Subsumption          : 0.03
% 2.26/1.27  Abstraction          : 0.01
% 2.26/1.27  MUC search           : 0.00
% 2.26/1.27  Cooper               : 0.00
% 2.26/1.27  Total                : 0.54
% 2.26/1.27  Index Insertion      : 0.00
% 2.26/1.27  Index Deletion       : 0.00
% 2.26/1.27  Index Matching       : 0.00
% 2.26/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
