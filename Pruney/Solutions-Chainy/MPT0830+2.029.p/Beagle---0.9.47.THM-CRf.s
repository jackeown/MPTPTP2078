%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:29 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 139 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 246 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_39])).

tff(c_45,plain,(
    ! [C_36,B_37,A_38] :
      ( v5_relat_1(C_36,B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_49,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_90,A_91,B_92] :
      ( r1_tarski(A_90,A_91)
      | ~ r1_tarski(A_90,k2_relat_1(B_92))
      | ~ v5_relat_1(B_92,A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_173,plain,(
    ! [B_17,A_16,A_91] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_17,A_16)),A_91)
      | ~ v5_relat_1(B_17,A_91)
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_162])).

tff(c_67,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_72,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(k7_relat_1(C_49,A_50))
      | ~ v4_relat_1(C_49,B_51)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_50] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_50))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_72])).

tff(c_77,plain,(
    ! [A_50] : v1_relat_1(k7_relat_1('#skF_4',A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_91,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(k7_relat_1(C_58,A_59),A_59)
      | ~ v4_relat_1(C_58,B_60)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,(
    ! [A_59] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_59),A_59)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_91])).

tff(c_99,plain,(
    ! [A_59] : v4_relat_1(k7_relat_1('#skF_4',A_59),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_95])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_221,plain,(
    ! [C_104,A_105,B_106] :
      ( m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ r1_tarski(k2_relat_1(C_104),B_106)
      | ~ r1_tarski(k1_relat_1(C_104),A_105)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_136,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k5_relset_1(A_76,B_77,C_78,D_79) = k7_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_139,plain,(
    ! [D_79] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_79) = k7_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_140,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_32])).

tff(c_224,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_221,c_140])).

tff(c_238,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_224])).

tff(c_245,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_248,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_99,c_248])).

tff(c_253,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_257,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_253])).

tff(c_264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_49,c_257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:33:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.28  
% 2.28/1.28  %Foreground sorts:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Background operators:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Foreground operators:
% 2.28/1.28  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.28  
% 2.28/1.30  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.28/1.30  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.28/1.30  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.28/1.30  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.30  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 2.28/1.30  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.28/1.30  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.28/1.30  tff(f_60, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.28/1.30  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.28/1.30  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.28/1.30  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.28/1.30  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.30  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.30  tff(c_36, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.28/1.30  tff(c_39, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.28/1.30  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_39])).
% 2.28/1.30  tff(c_45, plain, (![C_36, B_37, A_38]: (v5_relat_1(C_36, B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.28/1.30  tff(c_49, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.28/1.30  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.30  tff(c_78, plain, (![B_52, A_53]: (r1_tarski(k2_relat_1(B_52), A_53) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.30  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.30  tff(c_162, plain, (![A_90, A_91, B_92]: (r1_tarski(A_90, A_91) | ~r1_tarski(A_90, k2_relat_1(B_92)) | ~v5_relat_1(B_92, A_91) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.28/1.30  tff(c_173, plain, (![B_17, A_16, A_91]: (r1_tarski(k2_relat_1(k7_relat_1(B_17, A_16)), A_91) | ~v5_relat_1(B_17, A_91) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_22, c_162])).
% 2.28/1.30  tff(c_67, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.28/1.30  tff(c_71, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.28/1.30  tff(c_72, plain, (![C_49, A_50, B_51]: (v1_relat_1(k7_relat_1(C_49, A_50)) | ~v4_relat_1(C_49, B_51) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.30  tff(c_74, plain, (![A_50]: (v1_relat_1(k7_relat_1('#skF_4', A_50)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_71, c_72])).
% 2.28/1.30  tff(c_77, plain, (![A_50]: (v1_relat_1(k7_relat_1('#skF_4', A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74])).
% 2.28/1.30  tff(c_91, plain, (![C_58, A_59, B_60]: (v4_relat_1(k7_relat_1(C_58, A_59), A_59) | ~v4_relat_1(C_58, B_60) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.30  tff(c_95, plain, (![A_59]: (v4_relat_1(k7_relat_1('#skF_4', A_59), A_59) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_71, c_91])).
% 2.28/1.30  tff(c_99, plain, (![A_59]: (v4_relat_1(k7_relat_1('#skF_4', A_59), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95])).
% 2.28/1.30  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.30  tff(c_221, plain, (![C_104, A_105, B_106]: (m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~r1_tarski(k2_relat_1(C_104), B_106) | ~r1_tarski(k1_relat_1(C_104), A_105) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.28/1.30  tff(c_136, plain, (![A_76, B_77, C_78, D_79]: (k5_relset_1(A_76, B_77, C_78, D_79)=k7_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.28/1.30  tff(c_139, plain, (![D_79]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_79)=k7_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.28/1.30  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.28/1.30  tff(c_140, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_32])).
% 2.28/1.30  tff(c_224, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_221, c_140])).
% 2.28/1.30  tff(c_238, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_224])).
% 2.28/1.30  tff(c_245, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_238])).
% 2.28/1.30  tff(c_248, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_245])).
% 2.28/1.30  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_99, c_248])).
% 2.28/1.30  tff(c_253, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_238])).
% 2.28/1.30  tff(c_257, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_173, c_253])).
% 2.28/1.30  tff(c_264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_49, c_257])).
% 2.28/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  Inference rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Ref     : 0
% 2.28/1.30  #Sup     : 45
% 2.28/1.30  #Fact    : 0
% 2.28/1.30  #Define  : 0
% 2.28/1.30  #Split   : 1
% 2.28/1.30  #Chain   : 0
% 2.28/1.30  #Close   : 0
% 2.28/1.30  
% 2.28/1.30  Ordering : KBO
% 2.28/1.30  
% 2.28/1.30  Simplification rules
% 2.28/1.30  ----------------------
% 2.28/1.30  #Subsume      : 2
% 2.28/1.30  #Demod        : 18
% 2.28/1.30  #Tautology    : 5
% 2.28/1.30  #SimpNegUnit  : 0
% 2.28/1.30  #BackRed      : 1
% 2.28/1.30  
% 2.28/1.30  #Partial instantiations: 0
% 2.28/1.30  #Strategies tried      : 1
% 2.28/1.30  
% 2.28/1.30  Timing (in seconds)
% 2.28/1.30  ----------------------
% 2.28/1.30  Preprocessing        : 0.31
% 2.28/1.30  Parsing              : 0.17
% 2.28/1.30  CNF conversion       : 0.02
% 2.28/1.30  Main loop            : 0.22
% 2.28/1.30  Inferencing          : 0.09
% 2.28/1.30  Reduction            : 0.06
% 2.28/1.30  Demodulation         : 0.05
% 2.28/1.30  BG Simplification    : 0.01
% 2.28/1.30  Subsumption          : 0.04
% 2.28/1.30  Abstraction          : 0.01
% 2.28/1.30  MUC search           : 0.00
% 2.28/1.30  Cooper               : 0.00
% 2.28/1.30  Total                : 0.57
% 2.28/1.30  Index Insertion      : 0.00
% 2.28/1.30  Index Deletion       : 0.00
% 2.28/1.30  Index Matching       : 0.00
% 2.28/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
