%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:01 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 198 expanded)
%              Number of leaves         :   27 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :   60 ( 345 expanded)
%              Number of equality atoms :   17 (  99 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k7_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(c_22,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_35,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_72,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_47,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_35,c_72])).

tff(c_81,plain,(
    ! [A_48] : ~ r2_hidden(A_48,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_74])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_81])).

tff(c_94,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_2'(A_20),A_20)
      | A_20 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_22])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [A_5] : m1_subset_1('#skF_5',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_192,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k7_relset_1(A_85,B_86,C_87,D_88) = k9_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [A_85,B_86,D_88] : k7_relset_1(A_85,B_86,'#skF_5',D_88) = k9_relat_1('#skF_5',D_88) ),
    inference(resolution,[status(thm)],[c_99,c_192])).

tff(c_211,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( m1_subset_1(k7_relset_1(A_92,B_93,C_94,D_95),k1_zfmisc_1(B_93))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_221,plain,(
    ! [D_88,B_86,A_85] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_88),k1_zfmisc_1(B_86))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_211])).

tff(c_227,plain,(
    ! [D_96,B_97] : m1_subset_1(k9_relat_1('#skF_5',D_96),k1_zfmisc_1(B_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_221])).

tff(c_16,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_237,plain,(
    ! [B_97,A_9,D_96] :
      ( ~ v1_xboole_0(B_97)
      | ~ r2_hidden(A_9,k9_relat_1('#skF_5',D_96)) ) ),
    inference(resolution,[status(thm)],[c_227,c_16])).

tff(c_248,plain,(
    ! [A_101,D_102] : ~ r2_hidden(A_101,k9_relat_1('#skF_5',D_102)) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_257,plain,(
    ! [D_102] : k9_relat_1('#skF_5',D_102) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_94,c_248])).

tff(c_28,plain,(
    k7_relset_1(k1_xboole_0,'#skF_3','#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,(
    k7_relset_1('#skF_5','#skF_3','#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_28])).

tff(c_201,plain,(
    k9_relat_1('#skF_5','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_93])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_201])).

tff(c_266,plain,(
    ! [B_97] : ~ v1_xboole_0(B_97) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_101,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:05:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k7_relset_1 > k4_mcart_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.26/1.32  
% 2.26/1.32  %Foreground sorts:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Background operators:
% 2.26/1.32  
% 2.26/1.32  
% 2.26/1.32  %Foreground operators:
% 2.26/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.32  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.26/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.32  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.26/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.32  
% 2.26/1.33  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.26/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.33  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.26/1.33  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k7_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_2)).
% 2.26/1.33  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.26/1.33  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.26/1.33  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.26/1.33  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.26/1.33  tff(c_22, plain, (![A_20]: (r2_hidden('#skF_2'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.26/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.33  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.33  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.26/1.33  tff(c_35, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 2.26/1.33  tff(c_72, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.33  tff(c_74, plain, (![A_47]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_47, '#skF_5'))), inference(resolution, [status(thm)], [c_35, c_72])).
% 2.26/1.33  tff(c_81, plain, (![A_48]: (~r2_hidden(A_48, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_74])).
% 2.26/1.33  tff(c_90, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_81])).
% 2.26/1.33  tff(c_94, plain, (![A_20]: (r2_hidden('#skF_2'(A_20), A_20) | A_20='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_22])).
% 2.26/1.33  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.26/1.33  tff(c_99, plain, (![A_5]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_12])).
% 2.26/1.33  tff(c_192, plain, (![A_85, B_86, C_87, D_88]: (k7_relset_1(A_85, B_86, C_87, D_88)=k9_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.33  tff(c_200, plain, (![A_85, B_86, D_88]: (k7_relset_1(A_85, B_86, '#skF_5', D_88)=k9_relat_1('#skF_5', D_88))), inference(resolution, [status(thm)], [c_99, c_192])).
% 2.26/1.33  tff(c_211, plain, (![A_92, B_93, C_94, D_95]: (m1_subset_1(k7_relset_1(A_92, B_93, C_94, D_95), k1_zfmisc_1(B_93)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.33  tff(c_221, plain, (![D_88, B_86, A_85]: (m1_subset_1(k9_relat_1('#skF_5', D_88), k1_zfmisc_1(B_86)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(superposition, [status(thm), theory('equality')], [c_200, c_211])).
% 2.26/1.33  tff(c_227, plain, (![D_96, B_97]: (m1_subset_1(k9_relat_1('#skF_5', D_96), k1_zfmisc_1(B_97)))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_221])).
% 2.26/1.33  tff(c_16, plain, (![C_11, B_10, A_9]: (~v1_xboole_0(C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.33  tff(c_237, plain, (![B_97, A_9, D_96]: (~v1_xboole_0(B_97) | ~r2_hidden(A_9, k9_relat_1('#skF_5', D_96)))), inference(resolution, [status(thm)], [c_227, c_16])).
% 2.26/1.33  tff(c_248, plain, (![A_101, D_102]: (~r2_hidden(A_101, k9_relat_1('#skF_5', D_102)))), inference(splitLeft, [status(thm)], [c_237])).
% 2.26/1.33  tff(c_257, plain, (![D_102]: (k9_relat_1('#skF_5', D_102)='#skF_5')), inference(resolution, [status(thm)], [c_94, c_248])).
% 2.26/1.33  tff(c_28, plain, (k7_relset_1(k1_xboole_0, '#skF_3', '#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.26/1.33  tff(c_93, plain, (k7_relset_1('#skF_5', '#skF_3', '#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_28])).
% 2.26/1.33  tff(c_201, plain, (k9_relat_1('#skF_5', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_93])).
% 2.26/1.33  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_201])).
% 2.26/1.33  tff(c_266, plain, (![B_97]: (~v1_xboole_0(B_97))), inference(splitRight, [status(thm)], [c_237])).
% 2.26/1.33  tff(c_101, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2])).
% 2.26/1.33  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_101])).
% 2.26/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  Inference rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Ref     : 0
% 2.26/1.33  #Sup     : 48
% 2.26/1.33  #Fact    : 0
% 2.26/1.33  #Define  : 0
% 2.26/1.33  #Split   : 1
% 2.26/1.33  #Chain   : 0
% 2.26/1.33  #Close   : 0
% 2.26/1.33  
% 2.26/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 8
% 2.26/1.33  #Demod        : 30
% 2.26/1.33  #Tautology    : 25
% 2.26/1.33  #SimpNegUnit  : 1
% 2.26/1.33  #BackRed      : 16
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.26/1.34  Preprocessing        : 0.32
% 2.26/1.34  Parsing              : 0.17
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.20
% 2.26/1.34  Inferencing          : 0.07
% 2.26/1.34  Reduction            : 0.06
% 2.26/1.34  Demodulation         : 0.04
% 2.26/1.34  BG Simplification    : 0.01
% 2.26/1.34  Subsumption          : 0.03
% 2.26/1.34  Abstraction          : 0.02
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.55
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
