%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:09 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 169 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 303 expanded)
%              Number of equality atoms :   27 (  87 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_30,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_39,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_83,plain,(
    ! [C_48,B_49,A_50] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_83])).

tff(c_92,plain,(
    ! [A_51] : ~ r2_hidden(A_51,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_97,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_102,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_10])).

tff(c_180,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k8_relset_1(A_64,B_65,C_66,D_67) = k10_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    ! [A_64,B_65,D_67] : k8_relset_1(A_64,B_65,'#skF_4',D_67) = k10_relat_1('#skF_4',D_67) ),
    inference(resolution,[status(thm)],[c_102,c_180])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_18])).

tff(c_153,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_160,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_153])).

tff(c_165,plain,(
    ! [A_58,B_59] : k1_relset_1(A_58,B_59,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_160])).

tff(c_222,plain,(
    ! [A_77,B_78,C_79] :
      ( k8_relset_1(A_77,B_78,C_79,B_78) = k1_relset_1(A_77,B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_227,plain,(
    ! [A_77,B_78] : k8_relset_1(A_77,B_78,'#skF_4',B_78) = k1_relset_1(A_77,B_78,'#skF_4') ),
    inference(resolution,[status(thm)],[c_102,c_222])).

tff(c_231,plain,(
    ! [B_78] : k10_relat_1('#skF_4',B_78) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_165,c_227])).

tff(c_32,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_100,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_97,c_32])).

tff(c_200,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_100])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  
% 2.32/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.32/1.37  
% 2.32/1.37  %Foreground sorts:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Background operators:
% 2.32/1.37  
% 2.32/1.37  
% 2.32/1.37  %Foreground operators:
% 2.32/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.32/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.32/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.32/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.32/1.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.32/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.32/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.32/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.32/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.32/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.32/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.32/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.32/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.37  
% 2.32/1.39  tff(f_85, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.32/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.32/1.39  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.32/1.39  tff(f_94, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.32/1.39  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.32/1.39  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.32/1.39  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.32/1.39  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.32/1.39  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.32/1.39  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.32/1.39  tff(c_30, plain, (![A_20]: (r2_hidden('#skF_1'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.32/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.32/1.39  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.32/1.39  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.32/1.39  tff(c_39, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34])).
% 2.32/1.39  tff(c_83, plain, (![C_48, B_49, A_50]: (~v1_xboole_0(C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.32/1.39  tff(c_87, plain, (![A_50]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_39, c_83])).
% 2.32/1.39  tff(c_92, plain, (![A_51]: (~r2_hidden(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_87])).
% 2.32/1.39  tff(c_97, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.32/1.39  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.32/1.39  tff(c_102, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_10])).
% 2.32/1.39  tff(c_180, plain, (![A_64, B_65, C_66, D_67]: (k8_relset_1(A_64, B_65, C_66, D_67)=k10_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.32/1.39  tff(c_188, plain, (![A_64, B_65, D_67]: (k8_relset_1(A_64, B_65, '#skF_4', D_67)=k10_relat_1('#skF_4', D_67))), inference(resolution, [status(thm)], [c_102, c_180])).
% 2.32/1.39  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.32/1.39  tff(c_107, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_18])).
% 2.32/1.39  tff(c_153, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.32/1.39  tff(c_160, plain, (![A_58, B_59]: (k1_relset_1(A_58, B_59, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_102, c_153])).
% 2.32/1.39  tff(c_165, plain, (![A_58, B_59]: (k1_relset_1(A_58, B_59, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_160])).
% 2.32/1.39  tff(c_222, plain, (![A_77, B_78, C_79]: (k8_relset_1(A_77, B_78, C_79, B_78)=k1_relset_1(A_77, B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.32/1.39  tff(c_227, plain, (![A_77, B_78]: (k8_relset_1(A_77, B_78, '#skF_4', B_78)=k1_relset_1(A_77, B_78, '#skF_4'))), inference(resolution, [status(thm)], [c_102, c_222])).
% 2.32/1.39  tff(c_231, plain, (![B_78]: (k10_relat_1('#skF_4', B_78)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_165, c_227])).
% 2.32/1.39  tff(c_32, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.32/1.39  tff(c_100, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_97, c_32])).
% 2.32/1.39  tff(c_200, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_100])).
% 2.32/1.39  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_200])).
% 2.32/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.39  
% 2.32/1.39  Inference rules
% 2.32/1.39  ----------------------
% 2.32/1.39  #Ref     : 0
% 2.32/1.39  #Sup     : 47
% 2.32/1.39  #Fact    : 0
% 2.32/1.39  #Define  : 0
% 2.32/1.39  #Split   : 0
% 2.32/1.39  #Chain   : 0
% 2.32/1.39  #Close   : 0
% 2.32/1.39  
% 2.32/1.39  Ordering : KBO
% 2.32/1.39  
% 2.32/1.39  Simplification rules
% 2.32/1.39  ----------------------
% 2.32/1.39  #Subsume      : 3
% 2.32/1.39  #Demod        : 32
% 2.32/1.39  #Tautology    : 34
% 2.32/1.39  #SimpNegUnit  : 0
% 2.32/1.39  #BackRed      : 14
% 2.32/1.39  
% 2.32/1.39  #Partial instantiations: 0
% 2.32/1.39  #Strategies tried      : 1
% 2.32/1.39  
% 2.32/1.39  Timing (in seconds)
% 2.32/1.39  ----------------------
% 2.32/1.39  Preprocessing        : 0.34
% 2.32/1.39  Parsing              : 0.18
% 2.32/1.39  CNF conversion       : 0.02
% 2.32/1.39  Main loop            : 0.16
% 2.32/1.39  Inferencing          : 0.05
% 2.32/1.39  Reduction            : 0.05
% 2.32/1.39  Demodulation         : 0.04
% 2.32/1.39  BG Simplification    : 0.01
% 2.32/1.39  Subsumption          : 0.02
% 2.32/1.39  Abstraction          : 0.01
% 2.32/1.39  MUC search           : 0.00
% 2.32/1.39  Cooper               : 0.00
% 2.32/1.39  Total                : 0.53
% 2.32/1.39  Index Insertion      : 0.00
% 2.32/1.39  Index Deletion       : 0.00
% 2.32/1.39  Index Matching       : 0.00
% 2.32/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
