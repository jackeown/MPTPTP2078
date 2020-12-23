%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:27 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 110 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 173 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_76,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_67])).

tff(c_111,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_32,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(k7_relat_1(C_18,A_16))
      | ~ v4_relat_1(C_18,B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_16] :
      ( v1_relat_1(k7_relat_1('#skF_6',A_16))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_120,c_32])).

tff(c_125,plain,(
    ! [A_16] : v1_relat_1(k7_relat_1('#skF_6',A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_122])).

tff(c_224,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(k7_relat_1(C_87,A_88),A_88)
      | ~ v4_relat_1(C_87,B_89)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_230,plain,(
    ! [A_88] :
      ( v4_relat_1(k7_relat_1('#skF_6',A_88),A_88)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_120,c_224])).

tff(c_235,plain,(
    ! [A_88] : v4_relat_1(k7_relat_1('#skF_6',A_88),A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_230])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k7_relat_1(B_20,A_19),B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_169,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_tarski(A_74,C_75)
      | ~ r1_tarski(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_177,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,k2_zfmisc_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_74,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_846,plain,(
    ! [D_209,B_210,C_211,A_212] :
      ( m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(B_210,C_211)))
      | ~ r1_tarski(k1_relat_1(D_209),B_210)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(A_212,C_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1112,plain,(
    ! [A_233,B_234,C_235,A_236] :
      ( m1_subset_1(A_233,k1_zfmisc_1(k2_zfmisc_1(B_234,C_235)))
      | ~ r1_tarski(k1_relat_1(A_233),B_234)
      | ~ r1_tarski(A_233,k2_zfmisc_1(A_236,C_235)) ) ),
    inference(resolution,[status(thm)],[c_22,c_846])).

tff(c_1191,plain,(
    ! [A_247,B_248] :
      ( m1_subset_1(A_247,k1_zfmisc_1(k2_zfmisc_1(B_248,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(A_247),B_248)
      | ~ r1_tarski(A_247,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_177,c_1112])).

tff(c_728,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k5_relset_1(A_199,B_200,C_201,D_202) = k7_relat_1(C_201,D_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_735,plain,(
    ! [D_202] : k5_relset_1('#skF_3','#skF_5','#skF_6',D_202) = k7_relat_1('#skF_6',D_202) ),
    inference(resolution,[status(thm)],[c_48,c_728])).

tff(c_46,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_3','#skF_5','#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_737,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_46])).

tff(c_1212,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_4')
    | ~ r1_tarski(k7_relat_1('#skF_6','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1191,c_737])).

tff(c_1237,plain,(
    ~ r1_tarski(k7_relat_1('#skF_6','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1212])).

tff(c_1240,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_1237])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1240])).

tff(c_1245,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_4')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1212])).

tff(c_1264,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_6','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_1245])).

tff(c_1268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_235,c_1264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.55  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.44/1.55  
% 3.44/1.55  %Foreground sorts:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Background operators:
% 3.44/1.55  
% 3.44/1.55  
% 3.44/1.55  %Foreground operators:
% 3.44/1.55  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.44/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.44/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.44/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.44/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.55  
% 3.58/1.57  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 3.58/1.57  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.58/1.57  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.58/1.57  tff(f_67, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 3.58/1.57  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.58/1.57  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.58/1.57  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.58/1.57  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.58/1.57  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.58/1.57  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.58/1.57  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.57  tff(c_67, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.58/1.57  tff(c_76, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_67])).
% 3.58/1.57  tff(c_111, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.58/1.57  tff(c_120, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_111])).
% 3.58/1.57  tff(c_32, plain, (![C_18, A_16, B_17]: (v1_relat_1(k7_relat_1(C_18, A_16)) | ~v4_relat_1(C_18, B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.57  tff(c_122, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_6', A_16)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_120, c_32])).
% 3.58/1.57  tff(c_125, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_6', A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_122])).
% 3.58/1.57  tff(c_224, plain, (![C_87, A_88, B_89]: (v4_relat_1(k7_relat_1(C_87, A_88), A_88) | ~v4_relat_1(C_87, B_89) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.57  tff(c_230, plain, (![A_88]: (v4_relat_1(k7_relat_1('#skF_6', A_88), A_88) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_120, c_224])).
% 3.58/1.57  tff(c_235, plain, (![A_88]: (v4_relat_1(k7_relat_1('#skF_6', A_88), A_88))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_230])).
% 3.58/1.57  tff(c_26, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.58/1.57  tff(c_34, plain, (![B_20, A_19]: (r1_tarski(k7_relat_1(B_20, A_19), B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.58/1.57  tff(c_58, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.57  tff(c_66, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_58])).
% 3.58/1.57  tff(c_169, plain, (![A_74, C_75, B_76]: (r1_tarski(A_74, C_75) | ~r1_tarski(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.57  tff(c_177, plain, (![A_74]: (r1_tarski(A_74, k2_zfmisc_1('#skF_3', '#skF_5')) | ~r1_tarski(A_74, '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_169])).
% 3.58/1.57  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.58/1.57  tff(c_846, plain, (![D_209, B_210, C_211, A_212]: (m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(B_210, C_211))) | ~r1_tarski(k1_relat_1(D_209), B_210) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(A_212, C_211))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.58/1.57  tff(c_1112, plain, (![A_233, B_234, C_235, A_236]: (m1_subset_1(A_233, k1_zfmisc_1(k2_zfmisc_1(B_234, C_235))) | ~r1_tarski(k1_relat_1(A_233), B_234) | ~r1_tarski(A_233, k2_zfmisc_1(A_236, C_235)))), inference(resolution, [status(thm)], [c_22, c_846])).
% 3.58/1.57  tff(c_1191, plain, (![A_247, B_248]: (m1_subset_1(A_247, k1_zfmisc_1(k2_zfmisc_1(B_248, '#skF_5'))) | ~r1_tarski(k1_relat_1(A_247), B_248) | ~r1_tarski(A_247, '#skF_6'))), inference(resolution, [status(thm)], [c_177, c_1112])).
% 3.58/1.57  tff(c_728, plain, (![A_199, B_200, C_201, D_202]: (k5_relset_1(A_199, B_200, C_201, D_202)=k7_relat_1(C_201, D_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.58/1.57  tff(c_735, plain, (![D_202]: (k5_relset_1('#skF_3', '#skF_5', '#skF_6', D_202)=k7_relat_1('#skF_6', D_202))), inference(resolution, [status(thm)], [c_48, c_728])).
% 3.58/1.57  tff(c_46, plain, (~m1_subset_1(k5_relset_1('#skF_3', '#skF_5', '#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.57  tff(c_737, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_735, c_46])).
% 3.58/1.57  tff(c_1212, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_4') | ~r1_tarski(k7_relat_1('#skF_6', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_1191, c_737])).
% 3.58/1.57  tff(c_1237, plain, (~r1_tarski(k7_relat_1('#skF_6', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1212])).
% 3.58/1.57  tff(c_1240, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_1237])).
% 3.58/1.57  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1240])).
% 3.58/1.57  tff(c_1245, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_4')), '#skF_4')), inference(splitRight, [status(thm)], [c_1212])).
% 3.58/1.57  tff(c_1264, plain, (~v4_relat_1(k7_relat_1('#skF_6', '#skF_4'), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1245])).
% 3.58/1.57  tff(c_1268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_235, c_1264])).
% 3.58/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.57  
% 3.58/1.57  Inference rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Ref     : 0
% 3.58/1.57  #Sup     : 253
% 3.58/1.57  #Fact    : 0
% 3.58/1.57  #Define  : 0
% 3.58/1.57  #Split   : 4
% 3.58/1.57  #Chain   : 0
% 3.58/1.57  #Close   : 0
% 3.58/1.57  
% 3.58/1.57  Ordering : KBO
% 3.58/1.57  
% 3.58/1.57  Simplification rules
% 3.58/1.57  ----------------------
% 3.58/1.57  #Subsume      : 37
% 3.58/1.57  #Demod        : 94
% 3.58/1.57  #Tautology    : 27
% 3.58/1.57  #SimpNegUnit  : 1
% 3.58/1.57  #BackRed      : 2
% 3.58/1.57  
% 3.58/1.57  #Partial instantiations: 0
% 3.58/1.57  #Strategies tried      : 1
% 3.58/1.57  
% 3.58/1.57  Timing (in seconds)
% 3.58/1.57  ----------------------
% 3.58/1.57  Preprocessing        : 0.32
% 3.58/1.57  Parsing              : 0.17
% 3.58/1.57  CNF conversion       : 0.02
% 3.58/1.57  Main loop            : 0.48
% 3.58/1.57  Inferencing          : 0.18
% 3.58/1.57  Reduction            : 0.15
% 3.58/1.57  Demodulation         : 0.10
% 3.58/1.57  BG Simplification    : 0.02
% 3.58/1.57  Subsumption          : 0.09
% 3.58/1.57  Abstraction          : 0.02
% 3.58/1.57  MUC search           : 0.00
% 3.58/1.57  Cooper               : 0.00
% 3.58/1.57  Total                : 0.82
% 3.58/1.57  Index Insertion      : 0.00
% 3.58/1.57  Index Deletion       : 0.00
% 3.58/1.57  Index Matching       : 0.00
% 3.58/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
