%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 214 expanded)
%              Number of equality atoms :   30 (  74 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | r1_tarski(C,k8_relset_1(A,B,D,k7_relset_1(A,B,D,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_72,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_relset_1(A_38,B_39,C_40) = k1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_132,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_138,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_76,c_135])).

tff(c_139,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_138])).

tff(c_8,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k10_relat_1(B_11,k9_relat_1(B_11,A_10)))
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k7_relset_1(A_50,B_51,C_52,D_53) = k9_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_103,plain,(
    ! [D_53] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_53) = k9_relat_1('#skF_4',D_53) ),
    inference(resolution,[status(thm)],[c_36,c_100])).

tff(c_85,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k8_relset_1(A_43,B_44,C_45,D_46) = k10_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    ! [D_46] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_46) = k10_relat_1('#skF_4',D_46) ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_2','#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_30])).

tff(c_104,plain,(
    ~ r1_tarski('#skF_3',k10_relat_1('#skF_4',k9_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_89])).

tff(c_116,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_140,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_119])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_140])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_147,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_4])).

tff(c_167,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_72,A_73] :
      ( r1_tarski(A_72,A_73)
      | ~ r1_tarski(A_72,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_147,c_167])).

tff(c_190,plain,(
    ! [A_73] : r1_tarski('#skF_3',A_73) ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_146,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_152,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_146])).

tff(c_174,plain,(
    ~ r1_tarski('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_4',k7_relset_1('#skF_1','#skF_1','#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_152,c_30])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.23  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.95/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.23  
% 2.15/1.24  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r1_tarski(C, k8_relset_1(A, B, D, k7_relset_1(A, B, D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 2.15/1.24  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.15/1.24  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.15/1.24  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.15/1.24  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.15/1.24  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.15/1.24  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.15/1.24  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.15/1.24  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.15/1.24  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.15/1.24  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.24  tff(c_32, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.24  tff(c_43, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.15/1.24  tff(c_38, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.24  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.24  tff(c_72, plain, (![A_38, B_39, C_40]: (k1_relset_1(A_38, B_39, C_40)=k1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.15/1.24  tff(c_76, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_72])).
% 2.15/1.24  tff(c_132, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.24  tff(c_135, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_132])).
% 2.15/1.24  tff(c_138, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_76, c_135])).
% 2.15/1.24  tff(c_139, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_43, c_138])).
% 2.15/1.24  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.15/1.24  tff(c_44, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.15/1.24  tff(c_47, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.15/1.24  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_47])).
% 2.15/1.24  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k10_relat_1(B_11, k9_relat_1(B_11, A_10))) | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.15/1.24  tff(c_100, plain, (![A_50, B_51, C_52, D_53]: (k7_relset_1(A_50, B_51, C_52, D_53)=k9_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.15/1.24  tff(c_103, plain, (![D_53]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_53)=k9_relat_1('#skF_4', D_53))), inference(resolution, [status(thm)], [c_36, c_100])).
% 2.15/1.24  tff(c_85, plain, (![A_43, B_44, C_45, D_46]: (k8_relset_1(A_43, B_44, C_45, D_46)=k10_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.15/1.24  tff(c_88, plain, (![D_46]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_46)=k10_relat_1('#skF_4', D_46))), inference(resolution, [status(thm)], [c_36, c_85])).
% 2.15/1.24  tff(c_30, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_2', '#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.15/1.24  tff(c_89, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_30])).
% 2.15/1.24  tff(c_104, plain, (~r1_tarski('#skF_3', k10_relat_1('#skF_4', k9_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_89])).
% 2.15/1.24  tff(c_116, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_104])).
% 2.15/1.24  tff(c_119, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_116])).
% 2.15/1.24  tff(c_140, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_119])).
% 2.15/1.24  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_140])).
% 2.15/1.24  tff(c_145, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 2.15/1.24  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.24  tff(c_147, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_4])).
% 2.15/1.24  tff(c_167, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.24  tff(c_182, plain, (![A_72, A_73]: (r1_tarski(A_72, A_73) | ~r1_tarski(A_72, '#skF_1'))), inference(resolution, [status(thm)], [c_147, c_167])).
% 2.15/1.24  tff(c_190, plain, (![A_73]: (r1_tarski('#skF_3', A_73))), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.15/1.24  tff(c_146, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.15/1.24  tff(c_152, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_146])).
% 2.15/1.24  tff(c_174, plain, (~r1_tarski('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_4', k7_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_152, c_30])).
% 2.15/1.24  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_174])).
% 2.15/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  Inference rules
% 2.15/1.24  ----------------------
% 2.15/1.24  #Ref     : 0
% 2.15/1.24  #Sup     : 29
% 2.15/1.24  #Fact    : 0
% 2.15/1.24  #Define  : 0
% 2.15/1.24  #Split   : 1
% 2.15/1.24  #Chain   : 0
% 2.15/1.24  #Close   : 0
% 2.15/1.24  
% 2.15/1.24  Ordering : KBO
% 2.15/1.24  
% 2.15/1.24  Simplification rules
% 2.15/1.24  ----------------------
% 2.15/1.24  #Subsume      : 1
% 2.15/1.24  #Demod        : 23
% 2.15/1.24  #Tautology    : 15
% 2.15/1.24  #SimpNegUnit  : 1
% 2.15/1.24  #BackRed      : 7
% 2.15/1.24  
% 2.15/1.24  #Partial instantiations: 0
% 2.15/1.24  #Strategies tried      : 1
% 2.15/1.24  
% 2.15/1.24  Timing (in seconds)
% 2.15/1.24  ----------------------
% 2.15/1.24  Preprocessing        : 0.31
% 2.15/1.24  Parsing              : 0.16
% 2.15/1.24  CNF conversion       : 0.02
% 2.15/1.24  Main loop            : 0.16
% 2.15/1.24  Inferencing          : 0.06
% 2.15/1.24  Reduction            : 0.05
% 2.15/1.24  Demodulation         : 0.04
% 2.15/1.24  BG Simplification    : 0.01
% 2.15/1.24  Subsumption          : 0.03
% 2.15/1.24  Abstraction          : 0.01
% 2.15/1.24  MUC search           : 0.00
% 2.15/1.24  Cooper               : 0.00
% 2.15/1.24  Total                : 0.50
% 2.15/1.24  Index Insertion      : 0.00
% 2.15/1.24  Index Deletion       : 0.00
% 2.15/1.24  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
