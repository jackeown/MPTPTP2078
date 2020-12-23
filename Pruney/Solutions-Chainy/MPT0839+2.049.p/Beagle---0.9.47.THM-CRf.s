%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:28 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 150 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 297 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_44,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_55,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_58])).

tff(c_63,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) = k1_xboole_0
      | k2_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_63])).

tff(c_72,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_73,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | k1_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_76,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_73])).

tff(c_82,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_76])).

tff(c_140,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_149,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_140])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_174,plain,(
    ! [A_83,B_84,B_85] :
      ( r2_hidden('#skF_1'(A_83,B_84),B_85)
      | ~ r1_tarski(A_83,B_85)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [A_83,B_84,B_85] :
      ( m1_subset_1('#skF_1'(A_83,B_84),B_85)
      | ~ r1_tarski(A_83,B_85)
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_174,c_18])).

tff(c_308,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_322,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_308])).

tff(c_84,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [D_42] :
      ( ~ r2_hidden(D_42,k1_relset_1('#skF_5','#skF_4','#skF_6'))
      | ~ m1_subset_1(D_42,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_95,plain,(
    ! [B_56] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6'),B_56),'#skF_5')
      | r1_tarski(k1_relset_1('#skF_5','#skF_4','#skF_6'),B_56) ) ),
    inference(resolution,[status(thm)],[c_84,c_42])).

tff(c_342,plain,(
    ! [B_111] :
      ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_6'),B_111),'#skF_5')
      | r1_tarski(k1_relat_1('#skF_6'),B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_322,c_95])).

tff(c_347,plain,(
    ! [B_84] :
      ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
      | r1_tarski(k1_relat_1('#skF_6'),B_84) ) ),
    inference(resolution,[status(thm)],[c_195,c_342])).

tff(c_348,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_354,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_348])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_149,c_354])).

tff(c_362,plain,(
    ! [B_84] : r1_tarski(k1_relat_1('#skF_6'),B_84) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_397,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114,B_115),B_115)
      | r2_hidden('#skF_3'(A_114,B_115),A_114)
      | B_115 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_502,plain,(
    ! [B_126,A_127] :
      ( ~ r1_tarski(B_126,'#skF_2'(A_127,B_126))
      | r2_hidden('#skF_3'(A_127,B_126),A_127)
      | B_126 = A_127 ) ),
    inference(resolution,[status(thm)],[c_397,c_32])).

tff(c_519,plain,(
    ! [A_128] :
      ( r2_hidden('#skF_3'(A_128,k1_xboole_0),A_128)
      | k1_xboole_0 = A_128 ) ),
    inference(resolution,[status(thm)],[c_16,c_502])).

tff(c_618,plain,(
    ! [A_132] :
      ( ~ r1_tarski(A_132,'#skF_3'(A_132,k1_xboole_0))
      | k1_xboole_0 = A_132 ) ),
    inference(resolution,[status(thm)],[c_519,c_32])).

tff(c_622,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_362,c_618])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_622])).

tff(c_640,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_997,plain,(
    ! [A_195,B_196,C_197] :
      ( k2_relset_1(A_195,B_196,C_197) = k2_relat_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1008,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_997])).

tff(c_1012,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_1008])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1012])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  
% 3.12/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.12/1.46  
% 3.12/1.46  %Foreground sorts:
% 3.12/1.46  
% 3.12/1.46  
% 3.12/1.46  %Background operators:
% 3.12/1.46  
% 3.12/1.46  
% 3.12/1.46  %Foreground operators:
% 3.12/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.12/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.12/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.12/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.46  
% 3.12/1.48  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 3.12/1.48  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.12/1.48  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.12/1.48  tff(f_66, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.12/1.48  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.12/1.48  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.12/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.12/1.48  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.12/1.48  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.48  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.12/1.48  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.12/1.48  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.12/1.48  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.12/1.48  tff(c_44, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.12/1.48  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.48  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.12/1.48  tff(c_55, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.48  tff(c_58, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_55])).
% 3.12/1.48  tff(c_61, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_58])).
% 3.12/1.48  tff(c_63, plain, (![A_53]: (k1_relat_1(A_53)=k1_xboole_0 | k2_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.12/1.48  tff(c_70, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_63])).
% 3.12/1.48  tff(c_72, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70])).
% 3.12/1.48  tff(c_73, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | k1_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.12/1.48  tff(c_76, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_73])).
% 3.12/1.48  tff(c_82, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_76])).
% 3.12/1.48  tff(c_140, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.12/1.48  tff(c_149, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_140])).
% 3.12/1.48  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.12/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.48  tff(c_126, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.48  tff(c_174, plain, (![A_83, B_84, B_85]: (r2_hidden('#skF_1'(A_83, B_84), B_85) | ~r1_tarski(A_83, B_85) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_6, c_126])).
% 3.12/1.48  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.12/1.48  tff(c_195, plain, (![A_83, B_84, B_85]: (m1_subset_1('#skF_1'(A_83, B_84), B_85) | ~r1_tarski(A_83, B_85) | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_174, c_18])).
% 3.12/1.48  tff(c_308, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.12/1.48  tff(c_322, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_308])).
% 3.12/1.48  tff(c_84, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.12/1.48  tff(c_42, plain, (![D_42]: (~r2_hidden(D_42, k1_relset_1('#skF_5', '#skF_4', '#skF_6')) | ~m1_subset_1(D_42, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.12/1.48  tff(c_95, plain, (![B_56]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6'), B_56), '#skF_5') | r1_tarski(k1_relset_1('#skF_5', '#skF_4', '#skF_6'), B_56))), inference(resolution, [status(thm)], [c_84, c_42])).
% 3.12/1.48  tff(c_342, plain, (![B_111]: (~m1_subset_1('#skF_1'(k1_relat_1('#skF_6'), B_111), '#skF_5') | r1_tarski(k1_relat_1('#skF_6'), B_111))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_322, c_95])).
% 3.12/1.48  tff(c_347, plain, (![B_84]: (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | r1_tarski(k1_relat_1('#skF_6'), B_84))), inference(resolution, [status(thm)], [c_195, c_342])).
% 3.12/1.48  tff(c_348, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_347])).
% 3.12/1.48  tff(c_354, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_348])).
% 3.12/1.48  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_149, c_354])).
% 3.12/1.48  tff(c_362, plain, (![B_84]: (r1_tarski(k1_relat_1('#skF_6'), B_84))), inference(splitRight, [status(thm)], [c_347])).
% 3.12/1.48  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.48  tff(c_397, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114, B_115), B_115) | r2_hidden('#skF_3'(A_114, B_115), A_114) | B_115=A_114)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.48  tff(c_32, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.12/1.48  tff(c_502, plain, (![B_126, A_127]: (~r1_tarski(B_126, '#skF_2'(A_127, B_126)) | r2_hidden('#skF_3'(A_127, B_126), A_127) | B_126=A_127)), inference(resolution, [status(thm)], [c_397, c_32])).
% 3.12/1.48  tff(c_519, plain, (![A_128]: (r2_hidden('#skF_3'(A_128, k1_xboole_0), A_128) | k1_xboole_0=A_128)), inference(resolution, [status(thm)], [c_16, c_502])).
% 3.12/1.48  tff(c_618, plain, (![A_132]: (~r1_tarski(A_132, '#skF_3'(A_132, k1_xboole_0)) | k1_xboole_0=A_132)), inference(resolution, [status(thm)], [c_519, c_32])).
% 3.12/1.48  tff(c_622, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_362, c_618])).
% 3.12/1.48  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_622])).
% 3.12/1.48  tff(c_640, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 3.12/1.48  tff(c_997, plain, (![A_195, B_196, C_197]: (k2_relset_1(A_195, B_196, C_197)=k2_relat_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.12/1.48  tff(c_1008, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_997])).
% 3.12/1.48  tff(c_1012, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_640, c_1008])).
% 3.12/1.48  tff(c_1014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1012])).
% 3.12/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  Inference rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Ref     : 0
% 3.12/1.48  #Sup     : 189
% 3.12/1.48  #Fact    : 0
% 3.12/1.48  #Define  : 0
% 3.12/1.48  #Split   : 4
% 3.12/1.48  #Chain   : 0
% 3.12/1.48  #Close   : 0
% 3.12/1.48  
% 3.12/1.48  Ordering : KBO
% 3.12/1.48  
% 3.12/1.48  Simplification rules
% 3.12/1.48  ----------------------
% 3.12/1.48  #Subsume      : 11
% 3.12/1.48  #Demod        : 60
% 3.12/1.48  #Tautology    : 52
% 3.12/1.48  #SimpNegUnit  : 4
% 3.12/1.48  #BackRed      : 10
% 3.12/1.48  
% 3.12/1.48  #Partial instantiations: 0
% 3.12/1.48  #Strategies tried      : 1
% 3.12/1.48  
% 3.12/1.48  Timing (in seconds)
% 3.12/1.48  ----------------------
% 3.12/1.48  Preprocessing        : 0.32
% 3.12/1.48  Parsing              : 0.17
% 3.12/1.48  CNF conversion       : 0.02
% 3.12/1.48  Main loop            : 0.39
% 3.12/1.48  Inferencing          : 0.16
% 3.12/1.48  Reduction            : 0.11
% 3.12/1.48  Demodulation         : 0.07
% 3.12/1.48  BG Simplification    : 0.02
% 3.12/1.48  Subsumption          : 0.07
% 3.12/1.48  Abstraction          : 0.02
% 3.12/1.48  MUC search           : 0.00
% 3.12/1.48  Cooper               : 0.00
% 3.12/1.48  Total                : 0.75
% 3.12/1.48  Index Insertion      : 0.00
% 3.12/1.48  Index Deletion       : 0.00
% 3.12/1.48  Index Matching       : 0.00
% 3.12/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
