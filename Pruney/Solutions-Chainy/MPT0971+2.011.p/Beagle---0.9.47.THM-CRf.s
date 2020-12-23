%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 130 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 282 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_1'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_241,plain,(
    ! [A_113,B_114,C_115] :
      ( k1_relset_1(A_113,B_114,C_115) = k1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_250,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_241])).

tff(c_789,plain,(
    ! [B_170,A_171,C_172] :
      ( k1_xboole_0 = B_170
      | k1_relset_1(A_171,B_170,C_172) = A_171
      | ~ v1_funct_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_804,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_789])).

tff(c_811,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_250,c_804])).

tff(c_819,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_18,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_824,plain,(
    ! [C_45] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_45),'#skF_6')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_18])).

tff(c_875,plain,(
    ! [C_180] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_180),'#skF_6')
      | ~ r2_hidden(C_180,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_62,c_824])).

tff(c_54,plain,(
    ! [E_67] :
      ( k1_funct_1('#skF_9',E_67) != '#skF_8'
      | ~ r2_hidden(E_67,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_920,plain,(
    ! [C_184] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_184)) != '#skF_8'
      | ~ r2_hidden(C_184,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_875,c_54])).

tff(c_924,plain,(
    ! [C_45] :
      ( C_45 != '#skF_8'
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_920])).

tff(c_927,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_62,c_924])).

tff(c_194,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_194])).

tff(c_56,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_206,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_56])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_927,c_206])).

tff(c_930,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_304,plain,(
    ! [A_129,B_130,C_131] :
      ( m1_subset_1(k2_relset_1(A_129,B_130,C_131),k1_zfmisc_1(B_130))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_328,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_304])).

tff(c_334,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_328])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_338,plain,(
    r1_tarski(k2_relat_1('#skF_9'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_334,c_10])).

tff(c_132,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_8',B_93)
      | ~ r1_tarski(k2_relset_1('#skF_6','#skF_7','#skF_9'),B_93) ) ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_204,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_8',B_93)
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_138])).

tff(c_353,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_338,c_204])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_361,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_8',B_134)
      | ~ r1_tarski('#skF_7',B_134) ) ),
    inference(resolution,[status(thm)],[c_353,c_2])).

tff(c_32,plain,(
    ! [B_50,A_49] :
      ( ~ r1_tarski(B_50,A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_374,plain,(
    ! [B_135] :
      ( ~ r1_tarski(B_135,'#skF_8')
      | ~ r1_tarski('#skF_7',B_135) ) ),
    inference(resolution,[status(thm)],[c_361,c_32])).

tff(c_382,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_374])).

tff(c_940,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_382])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.47  
% 3.16/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.47  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.16/1.47  
% 3.16/1.47  %Foreground sorts:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Background operators:
% 3.16/1.47  
% 3.16/1.47  
% 3.16/1.47  %Foreground operators:
% 3.16/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.16/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.16/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.16/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.16/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.16/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.16/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.47  
% 3.16/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.16/1.48  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 3.16/1.48  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.48  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.16/1.48  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.48  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.48  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.48  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.16/1.48  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.16/1.48  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.48  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.16/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.48  tff(c_111, plain, (![A_84, B_85]: (~r2_hidden('#skF_1'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.48  tff(c_116, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_111])).
% 3.16/1.48  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.48  tff(c_80, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.48  tff(c_89, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_80])).
% 3.16/1.48  tff(c_62, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.48  tff(c_16, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_5'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.48  tff(c_60, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.48  tff(c_241, plain, (![A_113, B_114, C_115]: (k1_relset_1(A_113, B_114, C_115)=k1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.16/1.48  tff(c_250, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_241])).
% 3.16/1.48  tff(c_789, plain, (![B_170, A_171, C_172]: (k1_xboole_0=B_170 | k1_relset_1(A_171, B_170, C_172)=A_171 | ~v1_funct_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.48  tff(c_804, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_789])).
% 3.16/1.48  tff(c_811, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_250, c_804])).
% 3.16/1.48  tff(c_819, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_811])).
% 3.16/1.48  tff(c_18, plain, (![A_9, C_45]: (r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.48  tff(c_824, plain, (![C_45]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_45), '#skF_6') | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_819, c_18])).
% 3.16/1.48  tff(c_875, plain, (![C_180]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_180), '#skF_6') | ~r2_hidden(C_180, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_62, c_824])).
% 3.16/1.48  tff(c_54, plain, (![E_67]: (k1_funct_1('#skF_9', E_67)!='#skF_8' | ~r2_hidden(E_67, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.48  tff(c_920, plain, (![C_184]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_184))!='#skF_8' | ~r2_hidden(C_184, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_875, c_54])).
% 3.16/1.48  tff(c_924, plain, (![C_45]: (C_45!='#skF_8' | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_920])).
% 3.16/1.48  tff(c_927, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_62, c_924])).
% 3.16/1.48  tff(c_194, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.16/1.48  tff(c_203, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_194])).
% 3.16/1.48  tff(c_56, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.16/1.48  tff(c_206, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_56])).
% 3.16/1.48  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_927, c_206])).
% 3.16/1.48  tff(c_930, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_811])).
% 3.16/1.48  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.48  tff(c_304, plain, (![A_129, B_130, C_131]: (m1_subset_1(k2_relset_1(A_129, B_130, C_131), k1_zfmisc_1(B_130)) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.16/1.48  tff(c_328, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_203, c_304])).
% 3.16/1.48  tff(c_334, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_328])).
% 3.16/1.48  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.48  tff(c_338, plain, (r1_tarski(k2_relat_1('#skF_9'), '#skF_7')), inference(resolution, [status(thm)], [c_334, c_10])).
% 3.16/1.48  tff(c_132, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.48  tff(c_138, plain, (![B_93]: (r2_hidden('#skF_8', B_93) | ~r1_tarski(k2_relset_1('#skF_6', '#skF_7', '#skF_9'), B_93))), inference(resolution, [status(thm)], [c_56, c_132])).
% 3.16/1.48  tff(c_204, plain, (![B_93]: (r2_hidden('#skF_8', B_93) | ~r1_tarski(k2_relat_1('#skF_9'), B_93))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_138])).
% 3.16/1.48  tff(c_353, plain, (r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_338, c_204])).
% 3.16/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.48  tff(c_361, plain, (![B_134]: (r2_hidden('#skF_8', B_134) | ~r1_tarski('#skF_7', B_134))), inference(resolution, [status(thm)], [c_353, c_2])).
% 3.16/1.48  tff(c_32, plain, (![B_50, A_49]: (~r1_tarski(B_50, A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.48  tff(c_374, plain, (![B_135]: (~r1_tarski(B_135, '#skF_8') | ~r1_tarski('#skF_7', B_135))), inference(resolution, [status(thm)], [c_361, c_32])).
% 3.16/1.48  tff(c_382, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_374])).
% 3.16/1.49  tff(c_940, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_382])).
% 3.16/1.49  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_940])).
% 3.16/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.49  
% 3.16/1.49  Inference rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Ref     : 0
% 3.16/1.49  #Sup     : 173
% 3.16/1.49  #Fact    : 0
% 3.16/1.49  #Define  : 0
% 3.16/1.49  #Split   : 6
% 3.16/1.49  #Chain   : 0
% 3.16/1.49  #Close   : 0
% 3.16/1.49  
% 3.16/1.49  Ordering : KBO
% 3.16/1.49  
% 3.16/1.49  Simplification rules
% 3.16/1.49  ----------------------
% 3.16/1.49  #Subsume      : 16
% 3.16/1.49  #Demod        : 147
% 3.16/1.49  #Tautology    : 78
% 3.16/1.49  #SimpNegUnit  : 4
% 3.16/1.49  #BackRed      : 33
% 3.16/1.49  
% 3.16/1.49  #Partial instantiations: 0
% 3.16/1.49  #Strategies tried      : 1
% 3.16/1.49  
% 3.16/1.49  Timing (in seconds)
% 3.16/1.49  ----------------------
% 3.16/1.49  Preprocessing        : 0.35
% 3.16/1.49  Parsing              : 0.17
% 3.16/1.49  CNF conversion       : 0.03
% 3.16/1.49  Main loop            : 0.38
% 3.16/1.49  Inferencing          : 0.14
% 3.16/1.49  Reduction            : 0.12
% 3.16/1.49  Demodulation         : 0.08
% 3.16/1.49  BG Simplification    : 0.02
% 3.16/1.49  Subsumption          : 0.07
% 3.16/1.49  Abstraction          : 0.02
% 3.16/1.49  MUC search           : 0.00
% 3.16/1.49  Cooper               : 0.00
% 3.16/1.49  Total                : 0.77
% 3.16/1.49  Index Insertion      : 0.00
% 3.16/1.49  Index Deletion       : 0.00
% 3.16/1.49  Index Matching       : 0.00
% 3.16/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
