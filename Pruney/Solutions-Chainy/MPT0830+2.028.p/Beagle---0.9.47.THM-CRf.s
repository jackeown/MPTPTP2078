%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:29 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 154 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 269 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [B_28,A_29] :
      ( v1_relat_1(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_36])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_39])).

tff(c_45,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_20,plain,(
    ! [C_15,A_13,B_14] :
      ( v5_relat_1(k7_relat_1(C_15,A_13),B_14)
      | ~ v5_relat_1(C_15,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(k7_relat_1(C_15,A_13))
      | ~ v5_relat_1(C_15,B_14)
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_13] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_49,c_22])).

tff(c_54,plain,(
    ! [A_13] : v1_relat_1(k7_relat_1('#skF_4',A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_86,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(k7_relat_1(C_57,A_58),A_58)
      | ~ v4_relat_1(C_57,B_59)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [A_58] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_58),A_58)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_94,plain,(
    ! [A_58] : v4_relat_1(k7_relat_1('#skF_4',A_58),A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_90])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_228,plain,(
    ! [C_114,A_115,B_116] :
      ( m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ r1_tarski(k2_relat_1(C_114),B_116)
      | ~ r1_tarski(k1_relat_1(C_114),A_115)
      | ~ v1_relat_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_131,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k5_relset_1(A_75,B_76,C_77,D_78) = k7_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_134,plain,(
    ! [D_78] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_78) = k7_relat_1('#skF_4',D_78) ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_135,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_32])).

tff(c_231,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_228,c_135])).

tff(c_245,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_231])).

tff(c_252,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_255,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_252])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_94,c_255])).

tff(c_260,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_264,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_267,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_264])).

tff(c_276,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_267])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_49,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:22:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.32  
% 2.27/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.33  
% 2.27/1.33  %Foreground sorts:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Background operators:
% 2.27/1.33  
% 2.27/1.33  
% 2.27/1.33  %Foreground operators:
% 2.27/1.33  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.27/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.33  
% 2.27/1.34  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.34  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.27/1.34  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.34  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.34  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc22_relat_1)).
% 2.27/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.27/1.34  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.27/1.34  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.27/1.34  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.27/1.34  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.27/1.34  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.34  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.34  tff(c_36, plain, (![B_28, A_29]: (v1_relat_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.27/1.34  tff(c_39, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_36])).
% 2.27/1.34  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_39])).
% 2.27/1.34  tff(c_45, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.34  tff(c_49, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.27/1.34  tff(c_20, plain, (![C_15, A_13, B_14]: (v5_relat_1(k7_relat_1(C_15, A_13), B_14) | ~v5_relat_1(C_15, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.34  tff(c_22, plain, (![C_15, A_13, B_14]: (v1_relat_1(k7_relat_1(C_15, A_13)) | ~v5_relat_1(C_15, B_14) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.34  tff(c_51, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_49, c_22])).
% 2.27/1.34  tff(c_54, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51])).
% 2.27/1.34  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.34  tff(c_62, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.34  tff(c_66, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.27/1.34  tff(c_86, plain, (![C_57, A_58, B_59]: (v4_relat_1(k7_relat_1(C_57, A_58), A_58) | ~v4_relat_1(C_57, B_59) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.27/1.34  tff(c_90, plain, (![A_58]: (v4_relat_1(k7_relat_1('#skF_4', A_58), A_58) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_86])).
% 2.27/1.34  tff(c_94, plain, (![A_58]: (v4_relat_1(k7_relat_1('#skF_4', A_58), A_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_90])).
% 2.27/1.34  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.34  tff(c_228, plain, (![C_114, A_115, B_116]: (m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~r1_tarski(k2_relat_1(C_114), B_116) | ~r1_tarski(k1_relat_1(C_114), A_115) | ~v1_relat_1(C_114))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.34  tff(c_131, plain, (![A_75, B_76, C_77, D_78]: (k5_relset_1(A_75, B_76, C_77, D_78)=k7_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.27/1.34  tff(c_134, plain, (![D_78]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_78)=k7_relat_1('#skF_4', D_78))), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.27/1.34  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.27/1.34  tff(c_135, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_32])).
% 2.27/1.34  tff(c_231, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_228, c_135])).
% 2.27/1.34  tff(c_245, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_231])).
% 2.27/1.34  tff(c_252, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_245])).
% 2.27/1.34  tff(c_255, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_252])).
% 2.27/1.34  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_94, c_255])).
% 2.27/1.34  tff(c_260, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_245])).
% 2.27/1.34  tff(c_264, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_260])).
% 2.27/1.34  tff(c_267, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_264])).
% 2.27/1.34  tff(c_276, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_267])).
% 2.27/1.34  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_49, c_276])).
% 2.27/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  Inference rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Ref     : 0
% 2.27/1.34  #Sup     : 45
% 2.27/1.34  #Fact    : 0
% 2.27/1.34  #Define  : 0
% 2.27/1.34  #Split   : 1
% 2.27/1.34  #Chain   : 0
% 2.27/1.34  #Close   : 0
% 2.27/1.34  
% 2.27/1.34  Ordering : KBO
% 2.27/1.34  
% 2.27/1.34  Simplification rules
% 2.27/1.34  ----------------------
% 2.27/1.34  #Subsume      : 2
% 2.27/1.34  #Demod        : 48
% 2.27/1.34  #Tautology    : 13
% 2.27/1.34  #SimpNegUnit  : 0
% 2.27/1.34  #BackRed      : 1
% 2.27/1.34  
% 2.27/1.34  #Partial instantiations: 0
% 2.27/1.34  #Strategies tried      : 1
% 2.27/1.34  
% 2.27/1.34  Timing (in seconds)
% 2.27/1.34  ----------------------
% 2.27/1.34  Preprocessing        : 0.33
% 2.27/1.34  Parsing              : 0.18
% 2.27/1.34  CNF conversion       : 0.02
% 2.27/1.34  Main loop            : 0.21
% 2.27/1.34  Inferencing          : 0.08
% 2.27/1.34  Reduction            : 0.07
% 2.27/1.34  Demodulation         : 0.05
% 2.27/1.34  BG Simplification    : 0.01
% 2.27/1.34  Subsumption          : 0.03
% 2.27/1.34  Abstraction          : 0.01
% 2.27/1.34  MUC search           : 0.00
% 2.27/1.34  Cooper               : 0.00
% 2.27/1.34  Total                : 0.56
% 2.27/1.34  Index Insertion      : 0.00
% 2.27/1.34  Index Deletion       : 0.00
% 2.27/1.34  Index Matching       : 0.00
% 2.27/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
