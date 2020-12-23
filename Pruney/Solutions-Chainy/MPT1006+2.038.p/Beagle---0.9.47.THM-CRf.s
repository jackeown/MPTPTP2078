%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:07 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 238 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 461 expanded)
%              Number of equality atoms :   30 ( 120 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
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
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_30,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_39,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34])).

tff(c_140,plain,(
    ! [C_55,B_56,A_57] :
      ( ~ v1_xboole_0(C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39,c_140])).

tff(c_149,plain,(
    ! [A_58] : ~ r2_hidden(A_58,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_168,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_160,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_8])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [A_38] : v1_relat_1(k6_relat_1(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_44])).

tff(c_63,plain,(
    ! [A_40] : k1_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_123,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k10_relat_1(B_50,A_51),k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [A_51] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_51),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_123])).

tff(c_131,plain,(
    ! [A_51] : r1_tarski(k10_relat_1(k1_xboole_0,A_51),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_126])).

tff(c_155,plain,(
    ! [A_51] : r1_tarski(k10_relat_1('#skF_4',A_51),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_131])).

tff(c_159,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | A_16 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_30])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_261,plain,(
    ! [B_73,A_74,A_75] :
      ( ~ v1_xboole_0(B_73)
      | ~ r2_hidden(A_74,A_75)
      | ~ r1_tarski(A_75,B_73) ) ),
    inference(resolution,[status(thm)],[c_12,c_140])).

tff(c_265,plain,(
    ! [B_76,A_77] :
      ( ~ v1_xboole_0(B_76)
      | ~ r1_tarski(A_77,B_76)
      | A_77 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_159,c_261])).

tff(c_268,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0('#skF_4')
      | k10_relat_1('#skF_4',A_51) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_155,c_265])).

tff(c_280,plain,(
    ! [A_51] : k10_relat_1('#skF_4',A_51) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_268])).

tff(c_16,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_129,plain,(
    ! [A_11,A_51] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_11),A_51),A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_123])).

tff(c_133,plain,(
    ! [A_11,A_51] : r1_tarski(k10_relat_1(k6_relat_1(A_11),A_51),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_310,plain,(
    ! [A_83,A_84] :
      ( ~ v1_xboole_0(A_83)
      | k10_relat_1(k6_relat_1(A_83),A_84) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_133,c_265])).

tff(c_332,plain,(
    ! [A_85] :
      ( r1_tarski('#skF_4',A_85)
      | ~ v1_xboole_0(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_133])).

tff(c_173,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k8_relset_1(A_59,B_60,C_61,D_62) = k10_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_177,plain,(
    ! [A_59,B_60,A_3,D_62] :
      ( k8_relset_1(A_59,B_60,A_3,D_62) = k10_relat_1(A_3,D_62)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_12,c_173])).

tff(c_335,plain,(
    ! [A_59,B_60,D_62] :
      ( k8_relset_1(A_59,B_60,'#skF_4',D_62) = k10_relat_1('#skF_4',D_62)
      | ~ v1_xboole_0(k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_332,c_177])).

tff(c_363,plain,(
    ! [A_90,B_91,D_92] :
      ( k8_relset_1(A_90,B_91,'#skF_4',D_92) = '#skF_4'
      | ~ v1_xboole_0(k2_zfmisc_1(A_90,B_91)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_335])).

tff(c_367,plain,(
    ! [B_2,D_92] :
      ( k8_relset_1('#skF_4',B_2,'#skF_4',D_92) = '#skF_4'
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_363])).

tff(c_371,plain,(
    ! [B_2,D_92] : k8_relset_1('#skF_4',B_2,'#skF_4',D_92) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_367])).

tff(c_32,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_158,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_154,c_32])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.19  
% 2.38/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.19  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.38/1.19  
% 2.38/1.19  %Foreground sorts:
% 2.38/1.19  
% 2.38/1.19  
% 2.38/1.19  %Background operators:
% 2.38/1.19  
% 2.38/1.19  
% 2.38/1.19  %Foreground operators:
% 2.38/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.38/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.19  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.38/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.38/1.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.38/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.38/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.38/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.38/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.19  
% 2.38/1.20  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.38/1.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.20  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.38/1.20  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_funct_2)).
% 2.38/1.20  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.38/1.20  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.38/1.20  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.38/1.20  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.38/1.20  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.38/1.20  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.38/1.20  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.38/1.20  tff(c_30, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.38/1.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.38/1.20  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.20  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.20  tff(c_39, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34])).
% 2.38/1.20  tff(c_140, plain, (![C_55, B_56, A_57]: (~v1_xboole_0(C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.20  tff(c_144, plain, (![A_57]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_39, c_140])).
% 2.38/1.20  tff(c_149, plain, (![A_58]: (~r2_hidden(A_58, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_144])).
% 2.38/1.20  tff(c_154, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_149])).
% 2.38/1.20  tff(c_168, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_2])).
% 2.38/1.20  tff(c_160, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_8])).
% 2.38/1.20  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.38/1.20  tff(c_44, plain, (![A_38]: (v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.20  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_44])).
% 2.38/1.20  tff(c_63, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.38/1.20  tff(c_72, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_63])).
% 2.38/1.20  tff(c_123, plain, (![B_50, A_51]: (r1_tarski(k10_relat_1(B_50, A_51), k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.20  tff(c_126, plain, (![A_51]: (r1_tarski(k10_relat_1(k1_xboole_0, A_51), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_123])).
% 2.38/1.20  tff(c_131, plain, (![A_51]: (r1_tarski(k10_relat_1(k1_xboole_0, A_51), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_126])).
% 2.38/1.20  tff(c_155, plain, (![A_51]: (r1_tarski(k10_relat_1('#skF_4', A_51), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_131])).
% 2.38/1.20  tff(c_159, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | A_16='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_30])).
% 2.38/1.20  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.38/1.20  tff(c_261, plain, (![B_73, A_74, A_75]: (~v1_xboole_0(B_73) | ~r2_hidden(A_74, A_75) | ~r1_tarski(A_75, B_73))), inference(resolution, [status(thm)], [c_12, c_140])).
% 2.38/1.20  tff(c_265, plain, (![B_76, A_77]: (~v1_xboole_0(B_76) | ~r1_tarski(A_77, B_76) | A_77='#skF_4')), inference(resolution, [status(thm)], [c_159, c_261])).
% 2.38/1.20  tff(c_268, plain, (![A_51]: (~v1_xboole_0('#skF_4') | k10_relat_1('#skF_4', A_51)='#skF_4')), inference(resolution, [status(thm)], [c_155, c_265])).
% 2.38/1.20  tff(c_280, plain, (![A_51]: (k10_relat_1('#skF_4', A_51)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_268])).
% 2.38/1.20  tff(c_16, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.38/1.20  tff(c_20, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.38/1.20  tff(c_129, plain, (![A_11, A_51]: (r1_tarski(k10_relat_1(k6_relat_1(A_11), A_51), A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_123])).
% 2.38/1.20  tff(c_133, plain, (![A_11, A_51]: (r1_tarski(k10_relat_1(k6_relat_1(A_11), A_51), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_129])).
% 2.38/1.20  tff(c_310, plain, (![A_83, A_84]: (~v1_xboole_0(A_83) | k10_relat_1(k6_relat_1(A_83), A_84)='#skF_4')), inference(resolution, [status(thm)], [c_133, c_265])).
% 2.38/1.20  tff(c_332, plain, (![A_85]: (r1_tarski('#skF_4', A_85) | ~v1_xboole_0(A_85))), inference(superposition, [status(thm), theory('equality')], [c_310, c_133])).
% 2.38/1.20  tff(c_173, plain, (![A_59, B_60, C_61, D_62]: (k8_relset_1(A_59, B_60, C_61, D_62)=k10_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.20  tff(c_177, plain, (![A_59, B_60, A_3, D_62]: (k8_relset_1(A_59, B_60, A_3, D_62)=k10_relat_1(A_3, D_62) | ~r1_tarski(A_3, k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_12, c_173])).
% 2.38/1.20  tff(c_335, plain, (![A_59, B_60, D_62]: (k8_relset_1(A_59, B_60, '#skF_4', D_62)=k10_relat_1('#skF_4', D_62) | ~v1_xboole_0(k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_332, c_177])).
% 2.38/1.20  tff(c_363, plain, (![A_90, B_91, D_92]: (k8_relset_1(A_90, B_91, '#skF_4', D_92)='#skF_4' | ~v1_xboole_0(k2_zfmisc_1(A_90, B_91)))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_335])).
% 2.38/1.20  tff(c_367, plain, (![B_2, D_92]: (k8_relset_1('#skF_4', B_2, '#skF_4', D_92)='#skF_4' | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_363])).
% 2.38/1.20  tff(c_371, plain, (![B_2, D_92]: (k8_relset_1('#skF_4', B_2, '#skF_4', D_92)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_367])).
% 2.38/1.20  tff(c_32, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.38/1.20  tff(c_158, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_154, c_32])).
% 2.38/1.20  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_371, c_158])).
% 2.38/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.20  
% 2.38/1.20  Inference rules
% 2.38/1.20  ----------------------
% 2.38/1.20  #Ref     : 0
% 2.38/1.20  #Sup     : 81
% 2.38/1.20  #Fact    : 0
% 2.38/1.20  #Define  : 0
% 2.38/1.20  #Split   : 0
% 2.38/1.20  #Chain   : 0
% 2.38/1.20  #Close   : 0
% 2.38/1.20  
% 2.38/1.20  Ordering : KBO
% 2.38/1.20  
% 2.38/1.20  Simplification rules
% 2.38/1.20  ----------------------
% 2.38/1.20  #Subsume      : 3
% 2.38/1.20  #Demod        : 56
% 2.38/1.20  #Tautology    : 55
% 2.38/1.20  #SimpNegUnit  : 0
% 2.38/1.20  #BackRed      : 16
% 2.38/1.20  
% 2.38/1.20  #Partial instantiations: 0
% 2.38/1.20  #Strategies tried      : 1
% 2.38/1.20  
% 2.38/1.20  Timing (in seconds)
% 2.38/1.20  ----------------------
% 2.38/1.21  Preprocessing        : 0.29
% 2.38/1.21  Parsing              : 0.16
% 2.38/1.21  CNF conversion       : 0.02
% 2.38/1.21  Main loop            : 0.20
% 2.38/1.21  Inferencing          : 0.08
% 2.38/1.21  Reduction            : 0.07
% 2.38/1.21  Demodulation         : 0.05
% 2.38/1.21  BG Simplification    : 0.01
% 2.38/1.21  Subsumption          : 0.03
% 2.38/1.21  Abstraction          : 0.01
% 2.38/1.21  MUC search           : 0.00
% 2.38/1.21  Cooper               : 0.00
% 2.38/1.21  Total                : 0.52
% 2.38/1.21  Index Insertion      : 0.00
% 2.38/1.21  Index Deletion       : 0.00
% 2.38/1.21  Index Matching       : 0.00
% 2.38/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
