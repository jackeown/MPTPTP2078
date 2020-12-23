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
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   66 (  97 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 188 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_60,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),A_43)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_77,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_188,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k7_relset_1(A_90,B_91,C_92,D_93) = k9_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_199,plain,(
    ! [D_93] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_93) = k9_relat_1('#skF_6',D_93) ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_315,plain,(
    ! [A_114,B_115,C_116] :
      ( k7_relset_1(A_114,B_115,C_116,A_114) = k2_relset_1(A_114,B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_323,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_315])).

tff(c_327,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k9_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_323])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_332,plain,(
    r2_hidden('#skF_3',k9_relat_1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_40])).

tff(c_367,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden(k4_tarski('#skF_2'(A_119,B_120,C_121),A_119),C_121)
      | ~ r2_hidden(A_119,k9_relat_1(C_121,B_120))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_564,plain,(
    ! [C_162,A_163,B_164] :
      ( k1_funct_1(C_162,'#skF_2'(A_163,B_164,C_162)) = A_163
      | ~ v1_funct_1(C_162)
      | ~ r2_hidden(A_163,k9_relat_1(C_162,B_164))
      | ~ v1_relat_1(C_162) ) ),
    inference(resolution,[status(thm)],[c_367,c_28])).

tff(c_575,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_332,c_564])).

tff(c_593,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_46,c_575])).

tff(c_157,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_2'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_103,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    ! [A_54,B_7,A_6] :
      ( m1_subset_1(A_54,B_7)
      | ~ r2_hidden(A_54,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_1348,plain,(
    ! [A_224,B_225,C_226,B_227] :
      ( m1_subset_1('#skF_2'(A_224,B_225,C_226),B_227)
      | ~ r1_tarski(B_225,B_227)
      | ~ r2_hidden(A_224,k9_relat_1(C_226,B_225))
      | ~ v1_relat_1(C_226) ) ),
    inference(resolution,[status(thm)],[c_157,c_108])).

tff(c_1379,plain,(
    ! [B_227] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),B_227)
      | ~ r1_tarski('#skF_4',B_227)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_332,c_1348])).

tff(c_1409,plain,(
    ! [B_228] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),B_228)
      | ~ r1_tarski('#skF_4',B_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1379])).

tff(c_38,plain,(
    ! [E_33] :
      ( k1_funct_1('#skF_6',E_33) != '#skF_3'
      | ~ m1_subset_1(E_33,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1429,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1409,c_38])).

tff(c_1442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_593,c_1429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.57  
% 3.66/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.58  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.66/1.58  
% 3.66/1.58  %Foreground sorts:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Background operators:
% 3.66/1.58  
% 3.66/1.58  
% 3.66/1.58  %Foreground operators:
% 3.66/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.66/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.66/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.66/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.66/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.66/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.66/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.66/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.66/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.66/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.66/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.66/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.58  
% 3.66/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.66/1.59  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.66/1.59  tff(f_98, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.66/1.59  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.66/1.59  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.66/1.59  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.66/1.59  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.66/1.59  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.66/1.59  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.66/1.59  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.66/1.59  tff(c_60, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), A_43) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.66/1.59  tff(c_65, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_60, c_4])).
% 3.66/1.59  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.66/1.59  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.66/1.59  tff(c_67, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.66/1.59  tff(c_73, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_67])).
% 3.66/1.59  tff(c_77, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_73])).
% 3.66/1.59  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.66/1.59  tff(c_188, plain, (![A_90, B_91, C_92, D_93]: (k7_relset_1(A_90, B_91, C_92, D_93)=k9_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.66/1.59  tff(c_199, plain, (![D_93]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_93)=k9_relat_1('#skF_6', D_93))), inference(resolution, [status(thm)], [c_42, c_188])).
% 3.66/1.59  tff(c_315, plain, (![A_114, B_115, C_116]: (k7_relset_1(A_114, B_115, C_116, A_114)=k2_relset_1(A_114, B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.66/1.59  tff(c_323, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_315])).
% 3.66/1.59  tff(c_327, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k9_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_323])).
% 3.66/1.59  tff(c_40, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.66/1.59  tff(c_332, plain, (r2_hidden('#skF_3', k9_relat_1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_40])).
% 3.66/1.59  tff(c_367, plain, (![A_119, B_120, C_121]: (r2_hidden(k4_tarski('#skF_2'(A_119, B_120, C_121), A_119), C_121) | ~r2_hidden(A_119, k9_relat_1(C_121, B_120)) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.59  tff(c_28, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.66/1.59  tff(c_564, plain, (![C_162, A_163, B_164]: (k1_funct_1(C_162, '#skF_2'(A_163, B_164, C_162))=A_163 | ~v1_funct_1(C_162) | ~r2_hidden(A_163, k9_relat_1(C_162, B_164)) | ~v1_relat_1(C_162))), inference(resolution, [status(thm)], [c_367, c_28])).
% 3.66/1.59  tff(c_575, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_332, c_564])).
% 3.66/1.59  tff(c_593, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_46, c_575])).
% 3.66/1.59  tff(c_157, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_2'(A_71, B_72, C_73), B_72) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.66/1.59  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.66/1.59  tff(c_103, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.66/1.59  tff(c_108, plain, (![A_54, B_7, A_6]: (m1_subset_1(A_54, B_7) | ~r2_hidden(A_54, A_6) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_103])).
% 3.66/1.59  tff(c_1348, plain, (![A_224, B_225, C_226, B_227]: (m1_subset_1('#skF_2'(A_224, B_225, C_226), B_227) | ~r1_tarski(B_225, B_227) | ~r2_hidden(A_224, k9_relat_1(C_226, B_225)) | ~v1_relat_1(C_226))), inference(resolution, [status(thm)], [c_157, c_108])).
% 3.66/1.59  tff(c_1379, plain, (![B_227]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), B_227) | ~r1_tarski('#skF_4', B_227) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_332, c_1348])).
% 3.66/1.59  tff(c_1409, plain, (![B_228]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), B_228) | ~r1_tarski('#skF_4', B_228))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1379])).
% 3.66/1.59  tff(c_38, plain, (![E_33]: (k1_funct_1('#skF_6', E_33)!='#skF_3' | ~m1_subset_1(E_33, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.66/1.59  tff(c_1429, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3' | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1409, c_38])).
% 3.66/1.59  tff(c_1442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_593, c_1429])).
% 3.66/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.59  
% 3.66/1.59  Inference rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Ref     : 0
% 3.66/1.59  #Sup     : 329
% 3.66/1.59  #Fact    : 0
% 3.66/1.59  #Define  : 0
% 3.66/1.59  #Split   : 11
% 3.66/1.59  #Chain   : 0
% 3.66/1.59  #Close   : 0
% 3.66/1.59  
% 3.66/1.59  Ordering : KBO
% 3.66/1.59  
% 3.66/1.59  Simplification rules
% 3.66/1.59  ----------------------
% 3.66/1.59  #Subsume      : 29
% 3.66/1.59  #Demod        : 65
% 3.66/1.59  #Tautology    : 40
% 3.66/1.59  #SimpNegUnit  : 0
% 3.66/1.59  #BackRed      : 5
% 3.66/1.59  
% 3.66/1.59  #Partial instantiations: 0
% 3.66/1.59  #Strategies tried      : 1
% 3.66/1.59  
% 3.66/1.59  Timing (in seconds)
% 3.66/1.59  ----------------------
% 3.66/1.59  Preprocessing        : 0.30
% 3.66/1.59  Parsing              : 0.16
% 3.66/1.59  CNF conversion       : 0.02
% 3.66/1.59  Main loop            : 0.54
% 3.66/1.59  Inferencing          : 0.19
% 3.66/1.59  Reduction            : 0.15
% 3.66/1.59  Demodulation         : 0.11
% 3.66/1.59  BG Simplification    : 0.03
% 3.66/1.59  Subsumption          : 0.13
% 3.66/1.59  Abstraction          : 0.03
% 3.66/1.59  MUC search           : 0.00
% 3.66/1.59  Cooper               : 0.00
% 3.66/1.59  Total                : 0.87
% 3.66/1.59  Index Insertion      : 0.00
% 3.66/1.60  Index Deletion       : 0.00
% 3.66/1.60  Index Matching       : 0.00
% 3.66/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
