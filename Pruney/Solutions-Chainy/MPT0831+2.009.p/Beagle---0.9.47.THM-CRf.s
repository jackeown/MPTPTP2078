%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:33 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   66 (  78 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 117 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_48,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_81,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_90,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_22,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,C_13))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_54])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [C_102,B_103,A_104] :
      ( r2_hidden(C_102,B_103)
      | ~ r1_tarski(k1_zfmisc_1(A_104),B_103)
      | ~ r1_tarski(C_102,A_104) ) ),
    inference(resolution,[status(thm)],[c_10,c_160])).

tff(c_287,plain,(
    ! [C_111,B_112,A_113] :
      ( r2_hidden(C_111,k1_zfmisc_1(B_112))
      | ~ r1_tarski(C_111,A_113)
      | ~ r1_tarski(A_113,B_112) ) ),
    inference(resolution,[status(thm)],[c_24,c_256])).

tff(c_347,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_7',k1_zfmisc_1(B_120))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),B_120) ) ),
    inference(resolution,[status(thm)],[c_62,c_287])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_365,plain,(
    ! [B_123] :
      ( r1_tarski('#skF_7',B_123)
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),B_123) ) ),
    inference(resolution,[status(thm)],[c_347,c_8])).

tff(c_401,plain,(
    ! [B_126] :
      ( r1_tarski('#skF_7',k2_zfmisc_1(B_126,'#skF_4'))
      | ~ r1_tarski('#skF_5',B_126) ) ),
    inference(resolution,[status(thm)],[c_22,c_365])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_152,plain,(
    ! [A_19,A_74,B_75] :
      ( v4_relat_1(A_19,A_74)
      | ~ r1_tarski(A_19,k2_zfmisc_1(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_32,c_144])).

tff(c_419,plain,(
    ! [B_127] :
      ( v4_relat_1('#skF_7',B_127)
      | ~ r1_tarski('#skF_5',B_127) ) ),
    inference(resolution,[status(thm)],[c_401,c_152])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_422,plain,(
    ! [B_127] :
      ( k7_relat_1('#skF_7',B_127) = '#skF_7'
      | ~ v1_relat_1('#skF_7')
      | ~ r1_tarski('#skF_5',B_127) ) ),
    inference(resolution,[status(thm)],[c_419,c_34])).

tff(c_453,plain,(
    ! [B_130] :
      ( k7_relat_1('#skF_7',B_130) = '#skF_7'
      | ~ r1_tarski('#skF_5',B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_422])).

tff(c_467,plain,(
    k7_relat_1('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_48,c_453])).

tff(c_522,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k5_relset_1(A_137,B_138,C_139,D_140) = k7_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_529,plain,(
    ! [D_140] : k5_relset_1('#skF_5','#skF_4','#skF_7',D_140) = k7_relat_1('#skF_7',D_140) ),
    inference(resolution,[status(thm)],[c_50,c_522])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_5','#skF_4',k5_relset_1('#skF_5','#skF_4','#skF_7','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_530,plain,(
    ~ r2_relset_1('#skF_5','#skF_4',k7_relat_1('#skF_7','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_46])).

tff(c_531,plain,(
    ~ r2_relset_1('#skF_5','#skF_4','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_530])).

tff(c_620,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( r2_relset_1(A_157,B_158,C_159,C_159)
      | ~ m1_subset_1(D_160,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_636,plain,(
    ! [C_163] :
      ( r2_relset_1('#skF_5','#skF_4',C_163,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_620])).

tff(c_641,plain,(
    r2_relset_1('#skF_5','#skF_4','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_636])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.51  
% 2.43/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.51  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.79/1.51  
% 2.79/1.51  %Foreground sorts:
% 2.79/1.51  
% 2.79/1.51  
% 2.79/1.51  %Background operators:
% 2.79/1.51  
% 2.79/1.51  
% 2.79/1.51  %Foreground operators:
% 2.79/1.51  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.79/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.79/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.51  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.79/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.51  
% 2.79/1.53  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.79/1.53  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.53  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.79/1.53  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.53  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.79/1.53  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.79/1.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.53  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.53  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.53  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.79/1.53  tff(f_88, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.79/1.53  tff(c_48, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.79/1.53  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.79/1.53  tff(c_81, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.53  tff(c_90, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_50, c_81])).
% 2.79/1.53  tff(c_22, plain, (![A_11, C_13, B_12]: (r1_tarski(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, C_13)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.79/1.53  tff(c_54, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.53  tff(c_62, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_54])).
% 2.79/1.53  tff(c_24, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.79/1.53  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.53  tff(c_160, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.53  tff(c_256, plain, (![C_102, B_103, A_104]: (r2_hidden(C_102, B_103) | ~r1_tarski(k1_zfmisc_1(A_104), B_103) | ~r1_tarski(C_102, A_104))), inference(resolution, [status(thm)], [c_10, c_160])).
% 2.79/1.53  tff(c_287, plain, (![C_111, B_112, A_113]: (r2_hidden(C_111, k1_zfmisc_1(B_112)) | ~r1_tarski(C_111, A_113) | ~r1_tarski(A_113, B_112))), inference(resolution, [status(thm)], [c_24, c_256])).
% 2.79/1.53  tff(c_347, plain, (![B_120]: (r2_hidden('#skF_7', k1_zfmisc_1(B_120)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), B_120))), inference(resolution, [status(thm)], [c_62, c_287])).
% 2.79/1.53  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.53  tff(c_365, plain, (![B_123]: (r1_tarski('#skF_7', B_123) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), B_123))), inference(resolution, [status(thm)], [c_347, c_8])).
% 2.79/1.53  tff(c_401, plain, (![B_126]: (r1_tarski('#skF_7', k2_zfmisc_1(B_126, '#skF_4')) | ~r1_tarski('#skF_5', B_126))), inference(resolution, [status(thm)], [c_22, c_365])).
% 2.79/1.53  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.53  tff(c_144, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.79/1.53  tff(c_152, plain, (![A_19, A_74, B_75]: (v4_relat_1(A_19, A_74) | ~r1_tarski(A_19, k2_zfmisc_1(A_74, B_75)))), inference(resolution, [status(thm)], [c_32, c_144])).
% 2.79/1.53  tff(c_419, plain, (![B_127]: (v4_relat_1('#skF_7', B_127) | ~r1_tarski('#skF_5', B_127))), inference(resolution, [status(thm)], [c_401, c_152])).
% 2.79/1.53  tff(c_34, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.53  tff(c_422, plain, (![B_127]: (k7_relat_1('#skF_7', B_127)='#skF_7' | ~v1_relat_1('#skF_7') | ~r1_tarski('#skF_5', B_127))), inference(resolution, [status(thm)], [c_419, c_34])).
% 2.79/1.53  tff(c_453, plain, (![B_130]: (k7_relat_1('#skF_7', B_130)='#skF_7' | ~r1_tarski('#skF_5', B_130))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_422])).
% 2.79/1.53  tff(c_467, plain, (k7_relat_1('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_48, c_453])).
% 2.79/1.53  tff(c_522, plain, (![A_137, B_138, C_139, D_140]: (k5_relset_1(A_137, B_138, C_139, D_140)=k7_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.79/1.53  tff(c_529, plain, (![D_140]: (k5_relset_1('#skF_5', '#skF_4', '#skF_7', D_140)=k7_relat_1('#skF_7', D_140))), inference(resolution, [status(thm)], [c_50, c_522])).
% 2.79/1.53  tff(c_46, plain, (~r2_relset_1('#skF_5', '#skF_4', k5_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.79/1.53  tff(c_530, plain, (~r2_relset_1('#skF_5', '#skF_4', k7_relat_1('#skF_7', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_529, c_46])).
% 2.79/1.53  tff(c_531, plain, (~r2_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_530])).
% 2.79/1.53  tff(c_620, plain, (![A_157, B_158, C_159, D_160]: (r2_relset_1(A_157, B_158, C_159, C_159) | ~m1_subset_1(D_160, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.53  tff(c_636, plain, (![C_163]: (r2_relset_1('#skF_5', '#skF_4', C_163, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4'))))), inference(resolution, [status(thm)], [c_50, c_620])).
% 2.79/1.53  tff(c_641, plain, (r2_relset_1('#skF_5', '#skF_4', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_50, c_636])).
% 2.79/1.53  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_531, c_641])).
% 2.79/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.53  
% 2.79/1.53  Inference rules
% 2.79/1.53  ----------------------
% 2.79/1.53  #Ref     : 0
% 2.79/1.53  #Sup     : 127
% 2.79/1.53  #Fact    : 0
% 2.79/1.53  #Define  : 0
% 2.79/1.53  #Split   : 3
% 2.79/1.53  #Chain   : 0
% 2.79/1.53  #Close   : 0
% 2.79/1.53  
% 2.79/1.53  Ordering : KBO
% 2.79/1.53  
% 2.79/1.53  Simplification rules
% 2.79/1.53  ----------------------
% 2.79/1.53  #Subsume      : 13
% 2.79/1.53  #Demod        : 24
% 2.79/1.53  #Tautology    : 32
% 2.79/1.53  #SimpNegUnit  : 4
% 2.79/1.53  #BackRed      : 1
% 2.79/1.53  
% 2.79/1.53  #Partial instantiations: 0
% 2.79/1.53  #Strategies tried      : 1
% 2.79/1.53  
% 2.79/1.53  Timing (in seconds)
% 2.79/1.53  ----------------------
% 2.79/1.53  Preprocessing        : 0.32
% 2.79/1.53  Parsing              : 0.16
% 2.79/1.53  CNF conversion       : 0.02
% 2.79/1.53  Main loop            : 0.32
% 2.79/1.53  Inferencing          : 0.12
% 2.79/1.53  Reduction            : 0.09
% 2.79/1.53  Demodulation         : 0.05
% 2.79/1.53  BG Simplification    : 0.02
% 2.79/1.53  Subsumption          : 0.07
% 2.79/1.53  Abstraction          : 0.02
% 2.79/1.53  MUC search           : 0.00
% 2.79/1.53  Cooper               : 0.00
% 2.79/1.53  Total                : 0.68
% 2.79/1.53  Index Insertion      : 0.00
% 2.79/1.53  Index Deletion       : 0.00
% 2.79/1.53  Index Matching       : 0.00
% 2.79/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
