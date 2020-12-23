%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:38 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   67 (  79 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  105 ( 129 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_195,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_228,plain,(
    ! [C_87] :
      ( r2_relset_1('#skF_3','#skF_2',C_87,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_195])).

tff(c_241,plain,(
    r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_228])).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(k2_zfmisc_1(A_6,C_8),k2_zfmisc_1(B_7,C_8))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_zfmisc_1(A_9),k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,(
    ! [A_84,B_85,B_86] :
      ( r2_hidden(A_84,B_85)
      | ~ r1_tarski(B_86,B_85)
      | v1_xboole_0(B_86)
      | ~ m1_subset_1(A_84,B_86) ) ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_217,plain,(
    ! [A_84,B_10,A_9] :
      ( r2_hidden(A_84,k1_zfmisc_1(B_10))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ m1_subset_1(A_84,k1_zfmisc_1(A_9))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_209])).

tff(c_256,plain,(
    ! [A_93,B_94,A_95] :
      ( r2_hidden(A_93,k1_zfmisc_1(B_94))
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_95))
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_217])).

tff(c_270,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_5',k1_zfmisc_1(B_96))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_96) ) ),
    inference(resolution,[status(thm)],[c_44,c_256])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    ! [B_96] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_96))
      | v1_xboole_0(k1_zfmisc_1(B_96))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_96) ) ),
    inference(resolution,[status(thm)],[c_270,c_14])).

tff(c_288,plain,(
    ! [B_99] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_99))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),B_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_275])).

tff(c_341,plain,(
    ! [B_102] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_102,'#skF_2')))
      | ~ r1_tarski('#skF_3',B_102) ) ),
    inference(resolution,[status(thm)],[c_10,c_288])).

tff(c_34,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_376,plain,(
    ! [B_103] :
      ( v4_relat_1('#skF_5',B_103)
      | ~ r1_tarski('#skF_3',B_103) ) ),
    inference(resolution,[status(thm)],[c_341,c_34])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,A_21) = B_22
      | ~ v4_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_379,plain,(
    ! [B_103] :
      ( k7_relat_1('#skF_5',B_103) = '#skF_5'
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_3',B_103) ) ),
    inference(resolution,[status(thm)],[c_376,c_30])).

tff(c_438,plain,(
    ! [B_107] :
      ( k7_relat_1('#skF_5',B_107) = '#skF_5'
      | ~ r1_tarski('#skF_3',B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_379])).

tff(c_448,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_438])).

tff(c_159,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k5_relset_1(A_73,B_74,C_75,D_76) = k7_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_172,plain,(
    ! [D_76] : k5_relset_1('#skF_3','#skF_2','#skF_5',D_76) = k7_relat_1('#skF_5',D_76) ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_40,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k5_relset_1('#skF_3','#skF_2','#skF_5','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_173,plain,(
    ~ r2_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_40])).

tff(c_449,plain,(
    ~ r2_relset_1('#skF_3','#skF_2','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_173])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:06 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  
% 2.45/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.36  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.45/1.36  
% 2.45/1.36  %Foreground sorts:
% 2.45/1.36  
% 2.45/1.36  
% 2.45/1.36  %Background operators:
% 2.45/1.36  
% 2.45/1.36  
% 2.45/1.36  %Foreground operators:
% 2.45/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.36  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.45/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.36  
% 2.45/1.38  tff(f_102, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.45/1.38  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.45/1.38  tff(f_73, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.45/1.38  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.45/1.38  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.45/1.38  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.45/1.38  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.45/1.38  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.45/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.38  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.45/1.38  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.38  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.45/1.38  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.45/1.38  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.45/1.38  tff(c_195, plain, (![A_80, B_81, C_82, D_83]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.45/1.38  tff(c_228, plain, (![C_87]: (r2_relset_1('#skF_3', '#skF_2', C_87, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))))), inference(resolution, [status(thm)], [c_44, c_195])).
% 2.45/1.38  tff(c_241, plain, (r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_228])).
% 2.45/1.38  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.45/1.38  tff(c_28, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.45/1.38  tff(c_81, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.38  tff(c_88, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_81])).
% 2.45/1.38  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_88])).
% 2.45/1.38  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(k2_zfmisc_1(A_6, C_8), k2_zfmisc_1(B_7, C_8)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.45/1.38  tff(c_22, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.45/1.38  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k1_zfmisc_1(A_9), k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.45/1.38  tff(c_24, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.45/1.38  tff(c_103, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.45/1.38  tff(c_209, plain, (![A_84, B_85, B_86]: (r2_hidden(A_84, B_85) | ~r1_tarski(B_86, B_85) | v1_xboole_0(B_86) | ~m1_subset_1(A_84, B_86))), inference(resolution, [status(thm)], [c_24, c_103])).
% 2.45/1.38  tff(c_217, plain, (![A_84, B_10, A_9]: (r2_hidden(A_84, k1_zfmisc_1(B_10)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~m1_subset_1(A_84, k1_zfmisc_1(A_9)) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_12, c_209])).
% 2.45/1.38  tff(c_256, plain, (![A_93, B_94, A_95]: (r2_hidden(A_93, k1_zfmisc_1(B_94)) | ~m1_subset_1(A_93, k1_zfmisc_1(A_95)) | ~r1_tarski(A_95, B_94))), inference(negUnitSimplification, [status(thm)], [c_22, c_217])).
% 2.45/1.38  tff(c_270, plain, (![B_96]: (r2_hidden('#skF_5', k1_zfmisc_1(B_96)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_96))), inference(resolution, [status(thm)], [c_44, c_256])).
% 2.45/1.38  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.38  tff(c_275, plain, (![B_96]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_96)) | v1_xboole_0(k1_zfmisc_1(B_96)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_96))), inference(resolution, [status(thm)], [c_270, c_14])).
% 2.45/1.38  tff(c_288, plain, (![B_99]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_99)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), B_99))), inference(negUnitSimplification, [status(thm)], [c_22, c_275])).
% 2.45/1.38  tff(c_341, plain, (![B_102]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_102, '#skF_2'))) | ~r1_tarski('#skF_3', B_102))), inference(resolution, [status(thm)], [c_10, c_288])).
% 2.45/1.38  tff(c_34, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.45/1.38  tff(c_376, plain, (![B_103]: (v4_relat_1('#skF_5', B_103) | ~r1_tarski('#skF_3', B_103))), inference(resolution, [status(thm)], [c_341, c_34])).
% 2.45/1.38  tff(c_30, plain, (![B_22, A_21]: (k7_relat_1(B_22, A_21)=B_22 | ~v4_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.38  tff(c_379, plain, (![B_103]: (k7_relat_1('#skF_5', B_103)='#skF_5' | ~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', B_103))), inference(resolution, [status(thm)], [c_376, c_30])).
% 2.45/1.38  tff(c_438, plain, (![B_107]: (k7_relat_1('#skF_5', B_107)='#skF_5' | ~r1_tarski('#skF_3', B_107))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_379])).
% 2.45/1.38  tff(c_448, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_438])).
% 2.45/1.38  tff(c_159, plain, (![A_73, B_74, C_75, D_76]: (k5_relset_1(A_73, B_74, C_75, D_76)=k7_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.45/1.38  tff(c_172, plain, (![D_76]: (k5_relset_1('#skF_3', '#skF_2', '#skF_5', D_76)=k7_relat_1('#skF_5', D_76))), inference(resolution, [status(thm)], [c_44, c_159])).
% 2.45/1.38  tff(c_40, plain, (~r2_relset_1('#skF_3', '#skF_2', k5_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.45/1.38  tff(c_173, plain, (~r2_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_5', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_40])).
% 2.45/1.38  tff(c_449, plain, (~r2_relset_1('#skF_3', '#skF_2', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_173])).
% 2.45/1.38  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_449])).
% 2.45/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.38  
% 2.45/1.38  Inference rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Ref     : 0
% 2.45/1.38  #Sup     : 80
% 2.45/1.38  #Fact    : 0
% 2.45/1.38  #Define  : 0
% 2.45/1.38  #Split   : 1
% 2.45/1.38  #Chain   : 0
% 2.45/1.38  #Close   : 0
% 2.45/1.38  
% 2.45/1.38  Ordering : KBO
% 2.45/1.38  
% 2.45/1.38  Simplification rules
% 2.45/1.38  ----------------------
% 2.45/1.38  #Subsume      : 13
% 2.45/1.38  #Demod        : 19
% 2.45/1.38  #Tautology    : 20
% 2.45/1.38  #SimpNegUnit  : 16
% 2.45/1.38  #BackRed      : 2
% 2.45/1.38  
% 2.45/1.38  #Partial instantiations: 0
% 2.45/1.38  #Strategies tried      : 1
% 2.45/1.38  
% 2.45/1.38  Timing (in seconds)
% 2.45/1.38  ----------------------
% 2.45/1.38  Preprocessing        : 0.32
% 2.45/1.38  Parsing              : 0.17
% 2.45/1.38  CNF conversion       : 0.02
% 2.45/1.38  Main loop            : 0.25
% 2.45/1.38  Inferencing          : 0.10
% 2.45/1.38  Reduction            : 0.07
% 2.45/1.38  Demodulation         : 0.05
% 2.45/1.38  BG Simplification    : 0.01
% 2.45/1.38  Subsumption          : 0.05
% 2.45/1.38  Abstraction          : 0.02
% 2.45/1.38  MUC search           : 0.00
% 2.45/1.38  Cooper               : 0.00
% 2.45/1.38  Total                : 0.61
% 2.45/1.38  Index Insertion      : 0.00
% 2.45/1.38  Index Deletion       : 0.00
% 2.45/1.38  Index Matching       : 0.00
% 2.45/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
