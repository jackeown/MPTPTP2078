%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 133 expanded)
%              Number of leaves         :   43 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  105 ( 241 expanded)
%              Number of equality atoms :   39 (  92 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [D_42,A_43] : r2_hidden(D_42,k2_tarski(A_43,D_42)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_69])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_110,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_114,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_110])).

tff(c_169,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_172,plain,(
    ! [D_81] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',D_81) = k9_relat_1('#skF_5',D_81) ),
    inference(resolution,[status(thm)],[c_54,c_169])).

tff(c_164,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_168,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_164])).

tff(c_212,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_relset_1(A_94,B_95,C_96,A_94) = k2_relset_1(A_94,B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214,plain,(
    k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5',k1_tarski('#skF_3')) = k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_212])).

tff(c_216,plain,(
    k9_relat_1('#skF_5',k1_tarski('#skF_3')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_168,c_214])).

tff(c_28,plain,(
    ! [A_14,B_16] :
      ( k9_relat_1(A_14,k1_tarski(B_16)) = k11_relat_1(A_14,B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_226,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_28])).

tff(c_233,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_226])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,k1_relat_1(B_18))
      | k11_relat_1(B_18,A_17) = k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_207,plain,(
    ! [B_92,A_93] :
      ( k1_tarski(k1_funct_1(B_92,A_93)) = k11_relat_1(B_92,A_93)
      | ~ r2_hidden(A_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2352,plain,(
    ! [B_6783,A_6784] :
      ( k1_tarski(k1_funct_1(B_6783,A_6784)) = k11_relat_1(B_6783,A_6784)
      | ~ v1_funct_1(B_6783)
      | k11_relat_1(B_6783,A_6784) = k1_xboole_0
      | ~ v1_relat_1(B_6783) ) ),
    inference(resolution,[status(thm)],[c_30,c_207])).

tff(c_50,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_173,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_50])).

tff(c_2359,plain,
    ( k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | k11_relat_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2352,c_173])).

tff(c_2425,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_233,c_58,c_233,c_2359])).

tff(c_2430,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_168])).

tff(c_48,plain,(
    ! [D_39,C_38,A_36,B_37] :
      ( r2_hidden(k1_funct_1(D_39,C_38),k2_relset_1(A_36,B_37,D_39))
      | k1_xboole_0 = B_37
      | ~ r2_hidden(C_38,A_36)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(D_39,A_36,B_37)
      | ~ v1_funct_1(D_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2524,plain,(
    ! [C_38] :
      ( r2_hidden(k1_funct_1('#skF_5',C_38),k1_xboole_0)
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_38,k1_tarski('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')))
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2430,c_48])).

tff(c_2573,plain,(
    ! [C_38] :
      ( r2_hidden(k1_funct_1('#skF_5',C_38),k1_xboole_0)
      | k1_xboole_0 = '#skF_4'
      | ~ r2_hidden(C_38,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2524])).

tff(c_2576,plain,(
    ! [C_7650] :
      ( r2_hidden(k1_funct_1('#skF_5',C_7650),k1_xboole_0)
      | ~ r2_hidden(C_7650,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2573])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2579,plain,(
    ! [C_7650] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_5',C_7650))
      | ~ r2_hidden(C_7650,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2576,c_36])).

tff(c_2586,plain,(
    ! [C_7774] : ~ r2_hidden(C_7774,k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2579])).

tff(c_2600,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_72,c_2586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.61  
% 3.34/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.62  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.34/1.62  
% 3.34/1.62  %Foreground sorts:
% 3.34/1.62  
% 3.34/1.62  
% 3.34/1.62  %Background operators:
% 3.34/1.62  
% 3.34/1.62  
% 3.34/1.62  %Foreground operators:
% 3.34/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.34/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.62  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.34/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.34/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.34/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.34/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.62  
% 3.71/1.63  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.71/1.63  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.71/1.63  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.71/1.63  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.71/1.63  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.71/1.63  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.71/1.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.71/1.63  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.71/1.63  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.71/1.63  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.71/1.63  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.71/1.63  tff(f_97, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.71/1.63  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.71/1.63  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.71/1.63  tff(c_69, plain, (![D_42, A_43]: (r2_hidden(D_42, k2_tarski(A_43, D_42)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.71/1.63  tff(c_72, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_69])).
% 3.71/1.63  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.71/1.63  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.71/1.63  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.71/1.63  tff(c_56, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.71/1.63  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.71/1.63  tff(c_110, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.71/1.63  tff(c_114, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_110])).
% 3.71/1.63  tff(c_169, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.71/1.63  tff(c_172, plain, (![D_81]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', D_81)=k9_relat_1('#skF_5', D_81))), inference(resolution, [status(thm)], [c_54, c_169])).
% 3.71/1.63  tff(c_164, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.71/1.63  tff(c_168, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_164])).
% 3.71/1.63  tff(c_212, plain, (![A_94, B_95, C_96]: (k7_relset_1(A_94, B_95, C_96, A_94)=k2_relset_1(A_94, B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.71/1.63  tff(c_214, plain, (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5', k1_tarski('#skF_3'))=k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_212])).
% 3.71/1.63  tff(c_216, plain, (k9_relat_1('#skF_5', k1_tarski('#skF_3'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_168, c_214])).
% 3.71/1.63  tff(c_28, plain, (![A_14, B_16]: (k9_relat_1(A_14, k1_tarski(B_16))=k11_relat_1(A_14, B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.71/1.63  tff(c_226, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_216, c_28])).
% 3.71/1.63  tff(c_233, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_226])).
% 3.71/1.63  tff(c_30, plain, (![A_17, B_18]: (r2_hidden(A_17, k1_relat_1(B_18)) | k11_relat_1(B_18, A_17)=k1_xboole_0 | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.63  tff(c_207, plain, (![B_92, A_93]: (k1_tarski(k1_funct_1(B_92, A_93))=k11_relat_1(B_92, A_93) | ~r2_hidden(A_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.71/1.63  tff(c_2352, plain, (![B_6783, A_6784]: (k1_tarski(k1_funct_1(B_6783, A_6784))=k11_relat_1(B_6783, A_6784) | ~v1_funct_1(B_6783) | k11_relat_1(B_6783, A_6784)=k1_xboole_0 | ~v1_relat_1(B_6783))), inference(resolution, [status(thm)], [c_30, c_207])).
% 3.71/1.63  tff(c_50, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.71/1.63  tff(c_173, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_50])).
% 3.71/1.63  tff(c_2359, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | k11_relat_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2352, c_173])).
% 3.71/1.63  tff(c_2425, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_233, c_58, c_233, c_2359])).
% 3.71/1.63  tff(c_2430, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_168])).
% 3.71/1.63  tff(c_48, plain, (![D_39, C_38, A_36, B_37]: (r2_hidden(k1_funct_1(D_39, C_38), k2_relset_1(A_36, B_37, D_39)) | k1_xboole_0=B_37 | ~r2_hidden(C_38, A_36) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(D_39, A_36, B_37) | ~v1_funct_1(D_39))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.71/1.63  tff(c_2524, plain, (![C_38]: (r2_hidden(k1_funct_1('#skF_5', C_38), k1_xboole_0) | k1_xboole_0='#skF_4' | ~r2_hidden(C_38, k1_tarski('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))) | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2430, c_48])).
% 3.71/1.63  tff(c_2573, plain, (![C_38]: (r2_hidden(k1_funct_1('#skF_5', C_38), k1_xboole_0) | k1_xboole_0='#skF_4' | ~r2_hidden(C_38, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2524])).
% 3.71/1.63  tff(c_2576, plain, (![C_7650]: (r2_hidden(k1_funct_1('#skF_5', C_7650), k1_xboole_0) | ~r2_hidden(C_7650, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_2573])).
% 3.71/1.63  tff(c_36, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.71/1.63  tff(c_2579, plain, (![C_7650]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_5', C_7650)) | ~r2_hidden(C_7650, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_2576, c_36])).
% 3.71/1.63  tff(c_2586, plain, (![C_7774]: (~r2_hidden(C_7774, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2579])).
% 3.71/1.63  tff(c_2600, plain, $false, inference(resolution, [status(thm)], [c_72, c_2586])).
% 3.71/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.63  
% 3.71/1.63  Inference rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Ref     : 0
% 3.71/1.63  #Sup     : 262
% 3.71/1.63  #Fact    : 4
% 3.71/1.63  #Define  : 0
% 3.71/1.63  #Split   : 3
% 3.71/1.63  #Chain   : 0
% 3.71/1.63  #Close   : 0
% 3.71/1.63  
% 3.71/1.63  Ordering : KBO
% 3.71/1.63  
% 3.71/1.63  Simplification rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Subsume      : 43
% 3.71/1.63  #Demod        : 54
% 3.71/1.63  #Tautology    : 83
% 3.71/1.63  #SimpNegUnit  : 1
% 3.71/1.63  #BackRed      : 5
% 3.71/1.63  
% 3.71/1.63  #Partial instantiations: 3948
% 3.71/1.63  #Strategies tried      : 1
% 3.71/1.63  
% 3.71/1.63  Timing (in seconds)
% 3.71/1.63  ----------------------
% 3.71/1.63  Preprocessing        : 0.33
% 3.71/1.63  Parsing              : 0.17
% 3.71/1.63  CNF conversion       : 0.02
% 3.71/1.63  Main loop            : 0.52
% 3.71/1.63  Inferencing          : 0.30
% 3.71/1.63  Reduction            : 0.11
% 3.71/1.63  Demodulation         : 0.08
% 3.71/1.63  BG Simplification    : 0.03
% 3.71/1.63  Subsumption          : 0.05
% 3.71/1.63  Abstraction          : 0.02
% 3.71/1.63  MUC search           : 0.00
% 3.71/1.64  Cooper               : 0.00
% 3.71/1.64  Total                : 0.88
% 3.71/1.64  Index Insertion      : 0.00
% 3.71/1.64  Index Deletion       : 0.00
% 3.71/1.64  Index Matching       : 0.00
% 3.71/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
